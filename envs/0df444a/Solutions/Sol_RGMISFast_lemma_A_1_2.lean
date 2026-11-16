-- Prove2me | solution 2 for RGMISFast.lemma_A_1
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T05:27:36.258297+00:00
-- url     : https://prove2.me/submissions/37b3e1e6-1893-440b-849c-55e4178c2686

import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_GoodEvent
import Definitions.Def_RGMISFast_IsRootConnected
import Definitions.Def_RGMISFast_condLaw
import Definitions.Def_RGMISFast_rankLaw
import Mathlib
set_option maxHeartbeats 1000000

-- Source: Theorems.Thm_RGMISFast_lemma_5_1
set_option autoImplicit false


/-!
# Attached sets and disjoint percolation certificates

An attached set is a set of nonroots each of whose vertices is reachable from
some root inside the induced vertex set. The percolation certificate retains
all of its nonroots and rejects its external boundary. Distinct attached sets
have incompatible certificates. This is the deterministic disjointness step
in the attached-set neighborhood inequality.
-/

namespace RGMISGeneral.Polynomial

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Graph steps whose destination lies in a specified finite vertex set. -/
def stepWithin (G : SimpleGraph V) (S : Finset V) (v w : V) : Prop :=
  G.Adj v w ∧ w ∈ S

/-- Every nonroot is joined to some root using only the chosen vertices. -/
def Attached (G : SimpleGraph V) (A T : Finset V) : Prop :=
  Disjoint A T ∧ ∀ v ∈ T, ∃ a ∈ A,
    Relation.ReflTransGen (stepWithin G (A ∪ T)) a v

/-- Vertices outside the chosen set with a neighbor inside it. -/
noncomputable def externalBoundary (G : SimpleGraph V) (S : Finset V) : Finset V :=
  Finset.univ.filter fun w => w ∉ S ∧ ∃ v ∈ S, G.Adj v w

@[simp] theorem mem_externalBoundary {G : SimpleGraph V} {S : Finset V} {w : V} :
    w ∈ externalBoundary G S ↔ w ∉ S ∧ ∃ v ∈ S, G.Adj v w := by
  simp [externalBoundary]

/-- An outcome retains the nonroots and rejects the entire external boundary.
Roots are forced to be present separately, and need no coin toss. -/
def PercolationCertificate (G : SimpleGraph V) (A T : Finset V) (ω : V → Bool) : Prop :=
  (∀ v ∈ T, ω v = true) ∧ ∀ v ∈ externalBoundary G (A ∪ T), ω v = false

omit [Fintype V] in
theorem attached_empty (G : SimpleGraph V) (A : Finset V) : Attached G A ∅ := by
  simp [Attached]

theorem disjoint_externalBoundary (G : SimpleGraph V) (S : Finset V) :
    Disjoint S (externalBoundary G S) := by
  apply Finset.disjoint_left.mpr
  intro v hv hboundary
  exact (mem_externalBoundary.mp hboundary).1 hv

private theorem certificate_path_stays
    {G : SimpleGraph V} {A T U : Finset V} {ω : V → Bool}
    (hT : PercolationCertificate G A T ω)
    (hU : PercolationCertificate G A U ω)
    {a v : V} (ha : a ∈ A)
    (hpath : Relation.ReflTransGen (stepWithin G (A ∪ T)) a v) :
    v ∈ A ∪ U := by
  induction hpath with
  | refl => exact Finset.mem_union_left _ ha
  | @tail b c hpath hstep ih =>
      by_contra hc
      have hcb : c ∈ externalBoundary G (A ∪ U) :=
        mem_externalBoundary.mpr ⟨hc, b, ih, hstep.1⟩
      have hcT : c ∈ T := by
        rcases Finset.mem_union.mp hstep.2 with hca | hct
        · exact (hc (Finset.mem_union_left _ hca)).elim
        · exact hct
      have htrue := hT.1 c hcT
      have hfalse := hU.2 c hcb
      simp_all

/-- Two attached sets satisfying the same certificate must coincide. -/
theorem attached_certificate_unique
    {G : SimpleGraph V} {A T U : Finset V} {ω : V → Bool}
    (hT : Attached G A T) (hU : Attached G A U)
    (hcT : PercolationCertificate G A T ω)
    (hcU : PercolationCertificate G A U ω) : T = U := by
  have inclusion : ∀ {T U : Finset V}, Attached G A T →
      Attached G A U → PercolationCertificate G A T ω →
      PercolationCertificate G A U ω → T ⊆ U := by
    intro T U hT _ hcT hcU v hv
    obtain ⟨a, ha, hpath⟩ := hT.2 v hv
    have hin := certificate_path_stays hcT hcU ha hpath
    rcases Finset.mem_union.mp hin with hA | hU
    · exact (Finset.disjoint_left.mp hT.1 hA hv).elim
    · exact hU
  exact Finset.Subset.antisymm (inclusion hT hU hcT hcU)
    (inclusion hU hT hcU hcT)

/-- The events used in the percolation counting argument are pairwise disjoint. -/
theorem attached_certificate_disjoint
    {G : SimpleGraph V} {A T U : Finset V}
    (hT : Attached G A T) (hU : Attached G A U) (hne : T ≠ U) :
    Disjoint {ω | PercolationCertificate G A T ω}
      {ω | PercolationCertificate G A U ω} := by
  apply Set.disjoint_left.mpr
  intro ω hcT hcU
  exact hne (attached_certificate_unique hT hU hcT hcU)

end RGMISGeneral.Polynomial

/-!
# Finite Bernoulli encoding

All probabilities below are explicit finite sums of product weights. This
avoids any stochastic-process assumptions in the percolation counting step.
-/

namespace RGMISGeneral.Polynomial

open Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The mass of a finite independent Bernoulli outcome. -/
def bernoulliWeight (p : ℝ) (ω : V → Bool) : ℝ :=
  ∏ v, if ω v then p else 1 - p

omit [DecidableEq V] in
theorem bernoulliWeight_nonneg {p : ℝ} (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (ω : V → Bool) : 0 ≤ bernoulliWeight p ω := by
  apply Finset.prod_nonneg
  intro v _
  split <;> linarith

theorem sum_bernoulliWeight (p : ℝ) :
    ∑ ω : V → Bool, bernoulliWeight p ω = 1 := by
  unfold bernoulliWeight
  rw [← Fintype.prod_sum (fun (_ : V) (b : Bool) => if b then p else 1 - p)]
  simp

/-- A cylinder specifies present and absent coordinates. -/
def Cylinder (Y B : Finset V) (ω : V → Bool) : Prop :=
  (∀ v ∈ Y, ω v = true) ∧ ∀ v ∈ B, ω v = false

private theorem cylinder_indicator_product (Y B : Finset V)
    (p : ℝ) (ω : V → Bool) :
    (if Cylinder Y B ω then bernoulliWeight p ω else 0) =
      ∏ v, if (v ∈ Y → ω v = true) ∧ (v ∈ B → ω v = false)
        then (if ω v then p else 1 - p) else 0 := by
  by_cases h : Cylinder Y B ω
  · rw [if_pos h]
    apply Finset.prod_congr rfl
    intro v _
    simp only [if_pos (show (v ∈ Y → ω v = true) ∧ (v ∈ B → ω v = false) from ⟨h.1 v, h.2 v⟩)]
  · rw [if_neg h]
    symm
    have hex : ∃ v, ¬ ((v ∈ Y → ω v = true) ∧ (v ∈ B → ω v = false)) := by
      by_contra hnot
      apply h
      exact ⟨fun v hv => (not_not.mp (not_exists.mp hnot v)).1 hv,
        fun v hv => (not_not.mp (not_exists.mp hnot v)).2 hv⟩
    obtain ⟨v, hv⟩ := hex
    exact Finset.prod_eq_zero (Finset.mem_univ v) (if_neg hv)

/-- Exact cylinder probability in a finite independent Bernoulli space. -/
theorem cylinder_weight_sum (Y B : Finset V) (hdisj : Disjoint Y B) (p : ℝ) :
    ∑ ω : V → Bool, (if Cylinder Y B ω then bernoulliWeight p ω else 0) =
      p ^ Y.card * (1 - p) ^ B.card := by
  simp_rw [cylinder_indicator_product]
  rw [← Fintype.prod_sum (fun (v : V) (b : Bool) =>
    if (v ∈ Y → b = true) ∧ (v ∈ B → b = false)
      then (if b then p else 1 - p) else 0)]
  have hcoord : ∀ v : V,
      (∑ b : Bool, if (v ∈ Y → b = true) ∧ (v ∈ B → b = false)
        then (if b then p else 1 - p) else 0) =
        (if v ∈ Y then p else 1) * (if v ∈ B then 1 - p else 1) := by
    intro v
    have hd : v ∈ Y → v ∈ B → False := fun hy hb =>
      Finset.disjoint_left.mp hdisj hy hb
    by_cases hy : v ∈ Y <;> by_cases hb : v ∈ B <;>
      simp_all
  simp_rw [hcoord]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_ite_mem]

/-- Arbitrarily many incompatible cylinders have total weight at most one. -/
theorem sum_disjoint_cylinder_weights_le_one
    {ι : Type*} [DecidableEq ι] (F : Finset ι) (Y B : ι → Finset V)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (hdisj : ∀ i ∈ F, Disjoint (Y i) (B i))
    (hunique : ∀ ω, ∀ i ∈ F, ∀ j ∈ F,
      Cylinder (Y i) (B i) ω → Cylinder (Y j) (B j) ω → i = j) :
    ∑ i ∈ F, p ^ (Y i).card * (1 - p) ^ (B i).card ≤ 1 := by
  have hpoint (ω : V → Bool) :
      ∑ i ∈ F, (if Cylinder (Y i) (B i) ω then bernoulliWeight p ω else 0)
        ≤ bernoulliWeight p ω := by
    by_cases hex : ∃ i ∈ F, Cylinder (Y i) (B i) ω
    · obtain ⟨i, hi, hc⟩ := hex
      rw [Finset.sum_eq_single i]
      · simp [hc]
      · intro j hj hji
        rw [if_neg]
        intro hcj
        exact hji (hunique ω j hj i hi hcj hc)
      · exact fun hni => (hni hi).elim
    · have hz : ∀ i ∈ F, ¬ Cylinder (Y i) (B i) ω := by simpa using hex
      simp only [Finset.sum_congr rfl (fun i hi => if_neg (hz i hi)), Finset.sum_const_zero]
      exact bernoulliWeight_nonneg hp hp1 ω
  calc
    _ = ∑ i ∈ F, ∑ ω : V → Bool,
        (if Cylinder (Y i) (B i) ω then bernoulliWeight p ω else 0) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (cylinder_weight_sum (Y i) (B i) (hdisj i hi) p).symm
    _ = ∑ ω : V → Bool, ∑ i ∈ F,
        (if Cylinder (Y i) (B i) ω then bernoulliWeight p ω else 0) := Finset.sum_comm
    _ ≤ ∑ ω : V → Bool, bernoulliWeight p ω :=
      Finset.sum_le_sum fun ω _ => hpoint ω
    _ = 1 := sum_bernoulliWeight p

/-- The exact percolation inequality for any family of attached sets. -/
theorem attached_percolation_bound (G : SimpleGraph V) (A : Finset V)
    (F : Finset (Finset V)) (hF : ∀ T ∈ F, Attached G A T)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    ∑ T ∈ F, p ^ T.card * (1 - p) ^ (externalBoundary G (A ∪ T)).card ≤ 1 := by
  apply sum_disjoint_cylinder_weights_le_one F id
    (fun T => externalBoundary G (A ∪ T)) p hp hp1
  · intro T _
    exact Finset.disjoint_of_subset_left Finset.subset_union_right
      (disjoint_externalBoundary G (A ∪ T))
  · intro ω T hT U hU hcT hcU
    exact attached_certificate_unique (hF T hT) (hF U hU) hcT hcU

end RGMISGeneral.Polynomial

/-!
# The finite counting identity behind the survival drift

This file proves the combinatorial loss identity for one greedy deletion.
It does not assert that a rank process has a particular infinitesimal law;
that probability-theoretic step remains separate.
-/

namespace RGMISGeneral.Polynomial

open Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Nonroot arrivals which destroy the specified root-and-attached vertex set. -/
noncomputable def killingArrivals (G : SimpleGraph V) (A T : Finset V) : Finset V :=
  Finset.univ.filter fun w => w ∉ A ∧
    (w ∈ T ∨ ∃ v ∈ A ∪ T, G.Adj v w)

@[simp] theorem mem_killingArrivals {G : SimpleGraph V} {A T : Finset V} {w : V} :
    w ∈ killingArrivals G A T ↔
      w ∉ A ∧ (w ∈ T ∨ ∃ v ∈ A ∪ T, G.Adj v w) := by
  simp [killingArrivals]

/-- The killing neighborhood consists of the chosen nonroots and its boundary. -/
theorem killingArrivals_eq_union {G : SimpleGraph V} {A T : Finset V}
    (hdisj : Disjoint A T) :
    killingArrivals G A T = T ∪ externalBoundary G (A ∪ T) := by
  ext w
  have hd : w ∈ T → w ∉ A := fun ht ha => Finset.disjoint_left.mp hdisj ha ht
  simp only [mem_killingArrivals, Finset.mem_union, mem_externalBoundary]
  by_cases hT : w ∈ T <;> simp_all

theorem killingArrivals_card {G : SimpleGraph V} {A T : Finset V}
    (hdisj : Disjoint A T) :
    (killingArrivals G A T).card = T.card + (externalBoundary G (A ∪ T)).card := by
  rw [killingArrivals_eq_union hdisj, Finset.card_union_of_disjoint]
  exact Finset.disjoint_of_subset_left Finset.subset_union_right
    (disjoint_externalBoundary G (A ∪ T))


end RGMISGeneral.Polynomial


/-!
# The analytic neighborhood inequality from a percolation estimate

The combinatorial percolation inequality is an explicit hypothesis. The
analytic implication below is independent of how that hypothesis is obtained.
-/

namespace RGMISGeneral.Polynomial

open scoped BigOperators

/-- A finite, equally weighted Jensen inequality for the exponential. -/
theorem card_mul_exp_average_le_sum_exp {ι : Type*} (s : Finset ι)
    (hs : s.Nonempty) (f : ι → ℝ) :
    (s.card : ℝ) * Real.exp ((∑ i ∈ s, f i) / s.card) ≤ ∑ i ∈ s, Real.exp (f i) := by
  have hn : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_ne_zero
  let μ : ℝ := (∑ i ∈ s, f i) / s.card
  have hpoint (i : ι) : Real.exp μ * (1 + (f i - μ)) ≤ Real.exp (f i) := by
    calc
      Real.exp μ * (1 + (f i - μ)) ≤ Real.exp μ * Real.exp (f i - μ) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        linarith [Real.add_one_le_exp (f i - μ)]
      _ = Real.exp (f i) := by rw [← Real.exp_add]; congr 1; ring
  have hsum := Finset.sum_le_sum (fun i (_hi : i ∈ s) ↦ hpoint i)
  have hidentity : (∑ i ∈ s, Real.exp μ * (1 + (f i - μ))) =
      (s.card : ℝ) * Real.exp μ := by
    rw [← Finset.mul_sum]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
      nsmul_eq_mul]
    dsimp [μ]
    field_simp
    ring
  rw [hidentity] at hsum
  exact hsum

/-- Reparameterizing the Bernoulli probability avoids a boundary optimization:
`1 - exp (-x)` is always positive and dominates `x * exp (-x)`. -/
theorem exponential_probability_lower (x : ℝ) :
    x * Real.exp (-x) ≤ 1 - Real.exp (-x) := by
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  have hcancel : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]
    simp
  rw [hcancel] at h
  nlinarith

/-- The analytic form of the neighborhood inequality. It suffices to know
the mean degree is positive; individual lower degree bounds are not used.

The hypothesis is the whole family of Bernoulli percolation estimates. The
choice `p = 1 - exp (-k / d̄)` yields the exact factor `exp 1`, including the
case where the mean degree equals `k`. -/
theorem card_le_exp_mul_average_div_pow_of_percolation
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (d : ι → ℝ) (k : ℕ)
    (hk : 0 < k)
    (hd : 0 < (∑ i ∈ s, d i) / (s.card : ℝ))
    (hpercolation : ∀ p : ℝ, 0 < p → p < 1 →
      (∑ i ∈ s, p ^ k * (1 - p) ^ (d i - (k : ℝ))) ≤ 1) :
    (s.card : ℝ) ≤
      (Real.exp 1 * ((∑ i ∈ s, d i) / (s.card : ℝ)) / (k : ℝ)) ^ k := by
  have hnpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hn : (s.card : ℝ) ≠ 0 := ne_of_gt hnpos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hkpos
  let dbar : ℝ := (∑ i ∈ s, d i) / (s.card : ℝ)
  have hdbar : 0 < dbar := hd
  let x : ℝ := (k : ℝ) / dbar
  have hx : 0 < x := div_pos hkpos hdbar
  have hxd : x * dbar = (k : ℝ) := by
    dsimp [x]
    exact div_mul_cancel₀ _ hdbar.ne'
  let p : ℝ := 1 - Real.exp (-x)
  have hp : 0 < p := by
    dsimp [p]
    have h := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hx)
    linarith
  have hpone : p < 1 := by
    dsimp [p]
    linarith [Real.exp_pos (-x)]
  have honep : 1 - p = Real.exp (-x) := by dsimp [p]; ring
  have hpower (i : ι) : (1 - p) ^ (d i - (k : ℝ)) =
      Real.exp (-x * (d i - (k : ℝ))) := by
    rw [honep, Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  have hper := hpercolation p hp hpone
  simp_rw [hpower] at hper
  rw [← Finset.mul_sum] at hper
  have hjensen := card_mul_exp_average_le_sum_exp s hs
    (fun i ↦ -x * (d i - (k : ℝ)))
  have havg : (∑ i ∈ s, -x * (d i - (k : ℝ))) / (s.card : ℝ) =
      -x * (dbar - (k : ℝ)) := by
    rw [← Finset.mul_sum, Finset.sum_sub_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul]
    dsimp [dbar]
    field_simp
  rw [havg] at hjensen
  have hweighted := mul_le_mul_of_nonneg_left hjensen (pow_nonneg hp.le k)
  have hJ : (s.card : ℝ) * p ^ k * Real.exp (-x * (dbar - (k : ℝ))) ≤ 1 := by
    nlinarith [hper, hweighted]
  have hlower : x * Real.exp (-x) ≤ p := exponential_probability_lower x
  have hlowpow : (x * Real.exp (-x)) ^ k ≤ p ^ k :=
    pow_le_pow_left₀ (by positivity) hlower k
  have hlowmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hlowpow hnpos.le)
    (Real.exp_pos (-x * (dbar - (k : ℝ)))).le
  have hexpidentity :
      (x * Real.exp (-x)) ^ k * Real.exp (-x * (dbar - (k : ℝ))) =
        (x * Real.exp (-1)) ^ k := by
    calc
      _ = x ^ k * Real.exp ((k : ℝ) * (-x) + (-x * (dbar - (k : ℝ)))) := by
        rw [mul_pow, mul_assoc, ← Real.exp_nat_mul, ← Real.exp_add]
      _ = x ^ k * Real.exp (-(k : ℝ)) := by
        congr 2
        nlinarith [hxd]
      _ = (x * Real.exp (-1)) ^ k := by
        rw [mul_pow, ← Real.exp_nat_mul]
        congr 2
        ring
  have hlow : (s.card : ℝ) * (x * Real.exp (-1)) ^ k ≤ 1 := by
    calc
      _ = (s.card : ℝ) * (x * Real.exp (-x)) ^ k *
          Real.exp (-x * (dbar - (k : ℝ))) := by rw [mul_assoc, hexpidentity]
      _ ≤ (s.card : ℝ) * p ^ k * Real.exp (-x * (dbar - (k : ℝ))) := hlowmul
      _ ≤ 1 := hJ
  have hinverse : (x * Real.exp (-1)) ^ k * (Real.exp 1 * dbar / (k : ℝ)) ^ k = 1 := by
    rw [← mul_pow]
    have hbase : (x * Real.exp (-1)) * (Real.exp 1 * dbar / (k : ℝ)) = 1 := by
      rw [Real.exp_neg]
      dsimp [x]
      field_simp
    rw [hbase, one_pow]
  have hfinal := mul_le_mul_of_nonneg_right hlow
    (pow_nonneg (by positivity : 0 ≤ Real.exp 1 * dbar / (k : ℝ)) k)
  rw [mul_assoc, hinverse, mul_one, one_mul] at hfinal
  exact hfinal

/-- The corresponding lower bound on the total degree, in the form used
by a differential inequality for the expected number of attached sets. -/
theorem sum_ge_card_rpow_of_percolation
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (d : ι → ℝ) (k : ℕ)
    (hk : 0 < k)
    (hd : 0 < (∑ i ∈ s, d i) / (s.card : ℝ))
    (hpercolation : ∀ p : ℝ, 0 < p → p < 1 →
      (∑ i ∈ s, p ^ k * (1 - p) ^ (d i - (k : ℝ))) ≤ 1) :
    (k : ℝ) / Real.exp 1 * (s.card : ℝ) ^ (1 + (k : ℝ)⁻¹) ≤ ∑ i ∈ s, d i := by
  have hnpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hbound := card_le_exp_mul_average_div_pow_of_percolation s hs d k hk hd hpercolation
  have hbase : 0 ≤ Real.exp 1 * ((∑ i ∈ s, d i) / (s.card : ℝ)) / (k : ℝ) := by
    positivity
  have hroot := Real.rpow_le_rpow hnpos.le hbound (inv_nonneg.mpr hkpos.le)
  rw [Real.pow_rpow_inv_natCast hbase (Nat.ne_of_gt hk)] at hroot
  have hscaled := mul_le_mul_of_nonneg_left hroot
    (by positivity : 0 ≤ (k : ℝ) / Real.exp 1 * (s.card : ℝ))
  have hright : (k : ℝ) / Real.exp 1 * (s.card : ℝ) *
      (Real.exp 1 * ((∑ i ∈ s, d i) / (s.card : ℝ)) / (k : ℝ)) = ∑ i ∈ s, d i := by
    field_simp
  rw [hright] at hscaled
  rw [Real.rpow_add hnpos, Real.rpow_one]
  nlinarith [hscaled]

/-- Natural-degree version. The lower bound `k ≤ d i` both guarantees a
positive mean and identifies natural subtraction with real subtraction. -/
theorem card_le_exp_mul_average_div_pow_of_nat_percolation
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (d : ι → ℕ) (k : ℕ)
    (hk : 0 < k) (hd : ∀ i ∈ s, k ≤ d i)
    (hpercolation : ∀ p : ℝ, 0 < p → p < 1 →
      (∑ i ∈ s, p ^ k * (1 - p) ^ (d i - k)) ≤ 1) :
    (s.card : ℝ) ≤
      (Real.exp 1 * ((∑ i ∈ s, (d i : ℝ)) / (s.card : ℝ)) / (k : ℝ)) ^ k := by
  have hnpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : (s.card : ℝ) * (k : ℝ) ≤ ∑ i ∈ s, (d i : ℝ) := by
    calc
      _ = ∑ _i ∈ s, (k : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ by exact_mod_cast hd i hi)
  have hmean : 0 < (∑ i ∈ s, (d i : ℝ)) / (s.card : ℝ) :=
    div_pos ((mul_pos hnpos hkpos).trans_le hsum) hnpos
  apply card_le_exp_mul_average_div_pow_of_percolation s hs (fun i ↦ (d i : ℝ)) k hk hmean
  intro p hp hpone
  convert hpercolation p hp hpone using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Nat.cast_sub (hd i hi), Real.rpow_natCast]

/-- Total-degree version with natural degrees, ready to use with a finite
family of connected sets. -/
theorem sum_ge_card_rpow_of_nat_percolation
    {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (d : ι → ℕ) (k : ℕ)
    (hk : 0 < k) (hd : ∀ i ∈ s, k ≤ d i)
    (hpercolation : ∀ p : ℝ, 0 < p → p < 1 →
      (∑ i ∈ s, p ^ k * (1 - p) ^ (d i - k)) ≤ 1) :
    (k : ℝ) / Real.exp 1 * (s.card : ℝ) ^ (1 + (k : ℝ)⁻¹) ≤ ∑ i ∈ s, (d i : ℝ) := by
  have hnpos : (0 : ℝ) < s.card := by exact_mod_cast hs.card_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hsum : (s.card : ℝ) * (k : ℝ) ≤ ∑ i ∈ s, (d i : ℝ) := by
    calc
      _ = ∑ _i ∈ s, (k : ℝ) := by simp
      _ ≤ _ := Finset.sum_le_sum (fun i hi ↦ by exact_mod_cast hd i hi)
  have hmean : 0 < (∑ i ∈ s, (d i : ℝ)) / (s.card : ℝ) :=
    div_pos ((mul_pos hnpos hkpos).trans_le hsum) hnpos
  apply sum_ge_card_rpow_of_percolation s hs (fun i ↦ (d i : ℝ)) k hk hmean
  intro p hp hpone
  convert hpercolation p hp hpone using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Nat.cast_sub (hd i hi), Real.rpow_natCast]

end RGMISGeneral.Polynomial

/-!
# The attached-set neighborhood inequality

This is the unconditional combinatorial lemma from the manuscript, with
neighborhoods computed from the graph. The Bernoulli estimate is proved from
certificate disjointness rather than supplied as an assumption.
-/

namespace RGMISGeneral.Polynomial

open Classical
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The degree sum lower bound for any family of distinct attached `k`-sets. -/
theorem attached_neighborhood_inequality
    (G : SimpleGraph V) (A : Finset V) (F : Finset (Finset V))
    (k : ℕ) (hk : 0 < k)
    (hF : ∀ T ∈ F, Attached G A T ∧ T.card = k) :
    (k : ℝ) / Real.exp 1 * (F.card : ℝ) ^ (1 + (k : ℝ)⁻¹) ≤
      ∑ T ∈ F, ((killingArrivals G A T).card : ℝ) := by
  by_cases hempty : F = ∅
  · subst F
    simp [Real.zero_rpow (by positivity : (1 + (k : ℝ)⁻¹) ≠ 0)]
  have hn : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  apply sum_ge_card_rpow_of_nat_percolation F hn
    (fun T => (killingArrivals G A T).card) k hk
  · intro T hT
    rw [killingArrivals_card (hF T hT).1.1, (hF T hT).2]
    omega
  · intro p hp hp1
    have hper := attached_percolation_bound G A F (fun T hT => (hF T hT).1)
      p hp.le hp1.le
    convert hper using 1
    apply Finset.sum_congr rfl
    intro T hT
    rw [killingArrivals_card (hF T hT).1.1, (hF T hT).2]
    simp

end RGMISGeneral.Polynomial

open RGMISFast RGMISGeneral.Polynomial
lemma mission_attached_to_existing {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (A W : Finset V) (h : IsAttached H A W) : Attached H A W := by
  refine ⟨h.1,?_⟩
  intro w hw
  obtain ⟨u,hu,hr⟩ := h.2 w hw
  refine ⟨u,hu,?_⟩
  have hh := (SimpleGraph.reachable_iff_reflTransGen (G := restrictTo H (↑(A ∪ W))) u w).mp hr
  clear hw hr
  induction hh with
  | refl => exact .refl
  | tail hp hxy ih => exact ih.tail ⟨hxy.1,hxy.2.2⟩

lemma mission_degree_eq_existing {V : Type*} [Fintype V] [DecidableEq V]
    (H : SimpleGraph V) (u : V) (W : Finset V) : dW H u W = (killingArrivals H {u} W).card := by
  classical
  simp [dW,killingArrivals]

theorem RGMISFast.lemma_5_1 {V : Type*} [Fintype V] [DecidableEq V] (H : SimpleGraph V) (u : V) (k : ℕ)
    (hk : 1 ≤ k) (S : Finset (Finset V)) (hS : S.Nonempty)
    (hSk : ∀ W ∈ S, W.card = k ∧ IsAttached H {u} W) :
    (k / Real.exp 1) * (S.card : ℝ) ^ (1 / (k : ℝ)) ≤
      (1 / (S.card : ℝ)) * ∑ W ∈ S, (dW H u W : ℝ) := by
  have hspos : (0:ℝ) < S.card := by exact_mod_cast hS.card_pos
  have hb := attached_neighborhood_inequality H {u} S k hk
    (fun W hW => ⟨mission_attached_to_existing H {u} W (hSk W hW).2,(hSk W hW).1⟩)
  simp_rw [←mission_degree_eq_existing H u] at hb
  rw [Real.rpow_add hspos,Real.rpow_one] at hb
  have hh : (k / Real.exp 1) * (S.card : ℝ) ^ (1 / (k : ℝ)) ≤
      (∑ W ∈ S, (dW H u W : ℝ)) / (S.card : ℝ) := by
    apply (le_div_iff₀ hspos).mpr
    simp only [one_div]
    nlinarith [hb]
  simpa only [one_div,div_eq_inv_mul,mul_one] using hh



-- Source: Solutions.AttachedSubsets

/-!
# Extracting an attached set of any smaller size

This is the deterministic exploration step converting a large retained
component union into a certificate with exactly `k` nonroot vertices.
-/

namespace RGMISGeneral.Polynomial

open Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private theorem path_exits_set {R : V → V → Prop} {S : Finset V} {a v : V}
    (hpath : Relation.ReflTransGen R a v) (ha : a ∈ S) (hv : v ∉ S) :
    ∃ x ∈ S, ∃ y, y ∉ S ∧ R x y := by
  by_contra h
  have hclosed : ∀ x ∈ S, ∀ y, R x y → y ∈ S := by
    intro x hx y hxy
    by_contra hy
    exact h ⟨x, hx, y, hy, hxy⟩
  have hin : ∀ {x}, Relation.ReflTransGen R a x → x ∈ S := by
    intro x hx
    induction hx with
    | refl => exact ha
    | tail _ hxy ih => exact hclosed _ ih _ hxy
  exact hv (hin hpath)

/-- One may grow any proper attached subset by one vertex inside the larger set. -/
theorem attached_can_grow {G : SimpleGraph V} {A T U : Finset V}
    (hT : Attached G A T) (hU : Attached G A U)
    (_hsub : T ⊆ U) (hcard : T.card < U.card) :
    ∃ w ∈ U, w ∉ T ∧ Attached G A (insert w T) := by
  obtain ⟨v, hvU, hvT⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
  obtain ⟨a, ha, hpath⟩ := hU.2 v hvU
  have hvA : v ∉ A := fun hvA => Finset.disjoint_left.mp hU.1 hvA hvU
  have hvout : v ∉ A ∪ T := by simp [hvA, hvT]
  obtain ⟨x, hx, w, hwout, hxw⟩ :=
    path_exits_set hpath (Finset.mem_union_left T ha) hvout
  have hwA : w ∉ A := fun h => hwout (Finset.mem_union_left T h)
  have hwT : w ∉ T := fun h => hwout (Finset.mem_union_right A h)
  have hwU : w ∈ U := (Finset.mem_union.mp hxw.2).resolve_left hwA
  refine ⟨w, hwU, hwT, ?_, ?_⟩
  · exact Finset.disjoint_insert_right.mpr ⟨hwA, hT.1⟩
  · intro z hz
    have hmono : ∀ {v y}, stepWithin G (A ∪ T) v y →
        stepWithin G (A ∪ insert w T) v y := by
      intro v y h
      exact ⟨h.1, Finset.mem_union.mpr ((Finset.mem_union.mp h.2).imp id
        (fun hy => Finset.mem_insert_of_mem hy))⟩
    have hxPath : ∃ a ∈ A,
        Relation.ReflTransGen (stepWithin G (A ∪ T)) a x := by
      rcases Finset.mem_union.mp hx with hxA | hxT
      · exact ⟨x, hxA, .refl⟩
      · exact hT.2 x hxT
    rcases Finset.mem_insert.mp hz with hzw | hzT
    · subst z
      obtain ⟨b, hb, hbx⟩ := hxPath
      exact ⟨b, hb, (Relation.ReflTransGen.mono @hmono _ _ hbx).tail
        ⟨hxw.1, Finset.mem_union_right A (Finset.mem_insert_self w T)⟩⟩
    · obtain ⟨b, hb, hbz⟩ := hT.2 z hzT
      exact ⟨b, hb, Relation.ReflTransGen.mono @hmono _ _ hbz⟩

/-- A retained component union with at least `k` nonroots contains an attached
certificate of exactly `k` nonroots. -/
theorem exists_attached_subset_card {G : SimpleGraph V} {A U : Finset V}
    (hU : Attached G A U) (k : ℕ) (hk : k ≤ U.card) :
    ∃ T ⊆ U, Attached G A T ∧ T.card = k := by
  induction k with
  | zero => exact ⟨∅, Finset.empty_subset _, attached_empty G A, by simp⟩
  | succ k ih =>
      obtain ⟨T, hTU, hT, hTk⟩ := ih (by omega)
      obtain ⟨w, hwU, hwT, hTw⟩ := attached_can_grow hT hU hTU (by omega)
      refine ⟨insert w T, Finset.insert_subset hwU hTU, hTw, ?_⟩
      simp [Finset.card_insert_of_notMem hwT, hTk]

end RGMISGeneral.Polynomial

-- Source: Solutions.LowRankCounting
open RGMISFast
namespace LowRankCounting
open Classical RGMISGeneral.Polynomial
variable {V : Type*} [Fintype V] [DecidableEq V]

def RootConnected (G : SimpleGraph V) (u : V) (S : Finset V) : Prop :=
  u ∈ S ∧ ∀v∈S, Relation.ReflTransGen (stepWithin G S) u v
noncomputable def sets (G : SimpleGraph V) (u : V) (n : ℕ) : Finset (Finset V) :=
  Finset.univ.filter (fun S=>RootConnected G u S ∧ S.card=n+1)
@[simp] lemma mem_sets (G : SimpleGraph V) (u : V) (n : ℕ) (S : Finset V) :
    S∈sets G u n ↔ RootConnected G u S ∧ S.card=n+1 := by simp [sets]
lemma attached_erase {G : SimpleGraph V} {u : V} {S : Finset V} (h : RootConnected G u S) :
    Attached G {u} (S.erase u) := by
  refine ⟨by simp,?_⟩
  intro v hv
  refine ⟨u,by simp,?_⟩
  simpa [h.1] using h.2 v (Finset.mem_erase.mp hv).2
lemma root_of_attached {G : SimpleGraph V} {u : V} {T : Finset V} (h : Attached G {u} T) :
    RootConnected G u (insert u T) := by
  refine ⟨by simp,?_⟩
  intro v hv
  rcases Finset.mem_insert.mp hv with rfl | hv
  · exact .refl
  · obtain ⟨a,ha,hp⟩ := h.2 v hv
    have : a=u := by simpa using ha
    subst a
    simpa using hp
lemma path_exit {G : SimpleGraph V} {S U : Finset V} {a v : V}
    (hp : Relation.ReflTransGen (stepWithin G U) a v) (ha : a∈S) (hv : v∉S) :
    ∃x∈S,∃y, y∉S ∧ G.Adj x y ∧ y∈U := by
  by_contra hn
  have hc : ∀x∈S,∀y,stepWithin G U x y → y∈S := by
    intro x hx y hxy
    by_contra hy
    exact hn ⟨x,hx,y,hy,hxy⟩
  apply hv
  clear hv
  induction hp with
  | refl => exact ha
  | tail _ hxy ih => exact hc _ ih _ hxy
lemma boundary_degree (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (Δ : ℕ) (hd : ∀v,G.degree v ≤ Δ) : (externalBoundary G S).card ≤ S.card*Δ := by
  have hs : externalBoundary G S ⊆ S.biUnion (fun v=>G.neighborFinset v) := by
    intro w hw
    obtain ⟨_,v,hv,ha⟩ := mem_externalBoundary.mp hw
    exact Finset.mem_biUnion.mpr ⟨v,hv,(G.mem_neighborFinset v w).mpr ha⟩
  calc
    _ ≤ (S.biUnion (fun v=>G.neighborFinset v)).card := Finset.card_le_card hs
    _ ≤ ∑v∈S,(G.neighborFinset v).card := Finset.card_biUnion_le
    _ ≤ ∑_v∈S,Δ := Finset.sum_le_sum (fun v _=>by simpa using hd v)
    _ = _ := by simp
lemma count_succ (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (n Δ : ℕ)
    (hd : ∀v,G.degree v ≤ Δ) :
    (sets G u (n+1)).card ≤ (sets G u n).card*((n+1)*Δ) := by
  have hs : sets G u (n+1) ⊆ (sets G u n).biUnion (fun S=>(externalBoundary G S).image (fun w=>insert w S)) := by
    intro U hU
    obtain ⟨hc,hcard⟩ := (mem_sets G u (n+1) U).mp hU
    obtain ⟨T,hTU,hT,hTc⟩ := exists_attached_subset_card (attached_erase hc) n (by rw [Finset.card_erase_of_mem hc.1,hcard]; omega)
    let S := insert u T
    have hSc : S.card=n+1 := by
      have hu : u∉T := by simpa using Finset.disjoint_left.mp hT.1 (Finset.mem_singleton_self u)
      simp [S,Finset.card_insert_of_notMem hu,hTc]
    have hSU : S ⊆ U := Finset.insert_subset hc.1 (fun _ h=> (Finset.mem_erase.mp (hTU h)).2)
    obtain ⟨v,hvU,hvS⟩ := Finset.exists_mem_notMem_of_card_lt_card (show S.card<U.card by omega)
    obtain ⟨x,hx,w,hw,hadj,hwU⟩ := path_exit (hc.2 v hvU) (show u∈S by simp [S]) hvS
    have heq : insert w S = U := Finset.eq_of_subset_of_card_le (Finset.insert_subset hwU hSU) (by rw [Finset.card_insert_of_notMem hw,hSc,hcard])
    apply Finset.mem_biUnion.mpr
    refine ⟨S,(mem_sets G u n S).mpr ⟨root_of_attached hT,hSc⟩,?_⟩
    exact Finset.mem_image.mpr ⟨w,mem_externalBoundary.mpr ⟨hw,x,hx,hadj⟩,heq⟩
  calc
    _ ≤ _ := Finset.card_le_card hs
    _ ≤ ∑S∈sets G u n,((externalBoundary G S).image (fun w=>insert w S)).card := Finset.card_biUnion_le
    _ ≤ ∑_S∈sets G u n,(n+1)*Δ := by
      apply Finset.sum_le_sum
      intro S hS
      exact Finset.card_image_le.trans ((boundary_degree G S Δ hd).trans_eq (by rw [(mem_sets G u n S).mp hS |>.2]))
    _ = _ := by simp
lemma count_zero (G : SimpleGraph V) (u : V) : (sets G u 0).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro S hS T hT
  obtain ⟨hS,hSc⟩ := (mem_sets G u 0 S).mp hS
  obtain ⟨hT,hTc⟩ := (mem_sets G u 0 T).mp hT
  have h1 : S={u} := Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hS.1) (by simp at hSc; simp [hSc]) |>.symm
  have h2 : T={u} := Finset.eq_of_subset_of_card_le (Finset.singleton_subset_iff.mpr hT.1) (by simp at hTc; simp [hTc]) |>.symm
  rw [h1,h2]
lemma reach_mem {G : SimpleGraph V} {S : Finset V} {u v : V}
    (hu : u∈S) (hp : Relation.ReflTransGen (stepWithin G S) u v) : v∈S := by
  induction hp with
  | refl => exact hu
  | tail _ hs _ => exact hs.2
lemma internal_neighbor {G : SimpleGraph V} {S : Finset V} {u : V}
    (h : RootConnected G u S) (hc : 2 ≤ S.card) (v : V) (hv : v∈S) :
    ∃w∈S,G.Adj v w := by
  by_cases he : v=u
  · subst v
    obtain ⟨w,hw,hwout⟩ := Finset.exists_mem_notMem_of_card_lt_card (show ({u}:Finset V).card<S.card by simp only [Finset.card_singleton]; omega)
    obtain ⟨x,hx,y,hy,hxy,hyS⟩ := path_exit (h.2 w hw) (Finset.mem_singleton_self u) hwout
    have : x=u := by simpa using hx
    subst x
    exact ⟨y,hyS,hxy⟩
  · rcases (h.2 v hv).cases_tail with heq | ⟨w,hp,hs⟩
    · exact (he heq).elim
    · exact ⟨w,reach_mem h.1 hp,hs.1.symm⟩
lemma boundary_sharp (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (u : V) (Δ : ℕ)
    (hd : ∀v,G.degree v ≤ Δ) (h : RootConnected G u S) (hc : 2 ≤ S.card) :
    (externalBoundary G S).card ≤ S.card*(Δ-1) := by
  have hs : externalBoundary G S ⊆ S.biUnion (fun v=>G.neighborFinset v \ S) := by
    intro w hw
    obtain ⟨hw,v,hv,ha⟩ := mem_externalBoundary.mp hw
    exact Finset.mem_biUnion.mpr ⟨v,hv,Finset.mem_sdiff.mpr ⟨(G.mem_neighborFinset v w).mpr ha,hw⟩⟩
  calc
    _ ≤ (S.biUnion (fun v=>G.neighborFinset v \ S)).card := Finset.card_le_card hs
    _ ≤ ∑v∈S,(G.neighborFinset v \ S).card := Finset.card_biUnion_le
    _ ≤ ∑_v∈S,(Δ-1) := by
      apply Finset.sum_le_sum
      intro v hv
      obtain ⟨w,hw,ha⟩ := internal_neighbor h hc v hv
      have hn : 0 < (G.neighborFinset v ∩ S).card := Finset.card_pos.mpr ⟨w,Finset.mem_inter.mpr ⟨(G.mem_neighborFinset v w).mpr ha,hw⟩⟩
      have he := Finset.card_sdiff_add_card_inter (G.neighborFinset v) S
      have hb : (G.neighborFinset v).card ≤ Δ := by simpa using hd v
      omega
    _ = _ := by simp

theorem family_large (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (F : Finset (Finset V)) (k Δ : ℕ) (hΔ : 2 ≤ Δ) (hk3 : 3 ≤ k)
    (hdegree : ∀ v, G.degree v ≤ Δ)
    (hF : ∀ T ∈ F, Attached G {u} T ∧ T.card = k) :
    F.card ≤ (4 * Δ) ^ k := by
  have hk : 0 < k := by omega
  by_cases hempty : F = ∅
  · simp [hempty]
  have hnonempty : F.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let d : Finset V → ℕ := fun T ↦ (killingArrivals G {u} T).card
  have hdmin : ∀ T ∈ F, k ≤ d T := by
    intro T hT
    dsimp [d]
    rw [killingArrivals_card (hF T hT).1.1, (hF T hT).2]
    omega
  have hpercolation : ∀ p : ℝ, 0 < p → p < 1 →
      (∑ T ∈ F, p ^ k * (1 - p) ^ (d T - k)) ≤ 1 := by
    intro p hp hpone
    have h := attached_percolation_bound G {u} F (fun T hT ↦ (hF T hT).1) p hp.le hpone.le
    convert h using 1
    apply Finset.sum_congr rfl
    intro T hT
    dsimp [d]
    rw [killingArrivals_card (hF T hT).1.1, (hF T hT).2]
    simp
  have hbound := card_le_exp_mul_average_div_pow_of_nat_percolation F hnonempty d k hk hdmin hpercolation
  have hnpos : (0 : ℝ) < F.card := by exact_mod_cast hnonempty.card_pos
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hkone : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hΔreal : (2 : ℝ) ≤ Δ := by exact_mod_cast hΔ
  have hΔpos : (0 : ℝ) ≤ Δ := by positivity
  let avg : ℝ := (∑ T ∈ F, (d T : ℝ)) / F.card
  have havg_nonneg : 0 ≤ avg :=
    div_nonneg (Finset.sum_nonneg (fun T _ ↦ Nat.cast_nonneg (d T))) hnpos.le
  have hdmax : ∀ T ∈ F, d T ≤ k + (k + 1) * (Δ-1) := by
    intro T hT
    have hu : u∉T := by simpa using Finset.disjoint_left.mp (hF T hT).1.1 (Finset.mem_singleton_self u)
    have hc : (insert u T).card=k+1 := by simp [hu,(hF T hT).2]
    have hb := boundary_sharp G (insert u T) u Δ hdegree (root_of_attached (hF T hT).1) (by omega)
    dsimp [d]
    rw [killingArrivals_card (hF T hT).1.1,(hF T hT).2]
    simpa [hc] using Nat.add_le_add_left hb k
  have havg : avg ≤ (k : ℝ) + ((k : ℝ) + 1) * ((Δ : ℝ)-1) := by
    apply (div_le_iff₀ hnpos).mpr
    calc
      (∑ T ∈ F, (d T : ℝ)) ≤ ∑ _T ∈ F, ((k : ℝ) + ((k : ℝ) + 1) * ((Δ : ℝ)-1)) := by
        apply Finset.sum_le_sum
        intro T hT
        have hh := hdmax T hT
        have ht : (↑(d T) : ℝ) ≤ (k:ℝ)+((k:ℝ)+1)*((Δ-1:ℕ):ℝ) := by exact_mod_cast hh
        simpa only [Nat.cast_sub (by omega : 1 ≤ Δ),Nat.cast_one] using ht
      _ = _ := by simp; ring
  have hkthree : (3 : ℝ) ≤ k := by exact_mod_cast hk3
  have havg' : 3*avg ≤ 4*Δ*k := by
    have h := mul_nonneg hΔpos (show 0 ≤ (k:ℝ)-3 by linarith)
    nlinarith
  have heavg := mul_le_mul_of_nonneg_right Real.exp_one_lt_three.le havg_nonneg
  have hbase : Real.exp 1 * avg / (k : ℝ) ≤ 4 * Δ := by
    apply (div_le_iff₀ hkpos).mpr
    nlinarith [mul_nonneg hΔpos hkpos.le]
  have hpow := pow_le_pow_left₀
    (div_nonneg (mul_nonneg (Real.exp_pos 1).le havg_nonneg) hkpos.le) hbase k
  have hresult : (F.card : ℝ) ≤ ((4 * Δ : ℕ) : ℝ) ^ k := by
    push_cast
    exact hbound.trans hpow
  exact_mod_cast hresult



lemma count_bound (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (n Δ : ℕ)
    (hΔ : 2 ≤ Δ) (hd : ∀v,G.degree v ≤ Δ) : (sets G u n).card ≤ (4*Δ)^n := by
  have h0 := count_zero G u
  have h1 := count_succ G u 0 Δ hd
  have h2 := count_succ G u 1 Δ hd
  by_cases hn : 3 ≤ n
  · let F := (sets G u n).image (fun S=>S.erase u)
    have hinj : Set.InjOn (fun S : Finset V=>S.erase u) (sets G u n) := by
      intro S hS T hT he
      have hs := ((mem_sets G u n S).mp hS).1.1
      have ht := ((mem_sets G u n T).mp hT).1.1
      calc
        S = insert u (S.erase u) := (Finset.insert_erase hs).symm
        _ = insert u (T.erase u) := congrArg (insert u) he
        _ = T := Finset.insert_erase ht
    have hcard : F.card=(sets G u n).card := Finset.card_image_iff.mpr hinj
    rw [← hcard]
    apply family_large G u F n Δ hΔ hn hd
    intro T hT
    obtain ⟨S,hS,rfl⟩ := Finset.mem_image.mp hT
    obtain ⟨hc,hs⟩ := (mem_sets G u n S).mp hS
    exact ⟨attached_erase hc,by rw [Finset.card_erase_of_mem hc.1,hs]; omega⟩
  · interval_cases n <;> norm_num at *
    · exact h0
    · nlinarith
    · have hb : (sets G u 1).card ≤ Δ := by nlinarith
      have hh := Nat.mul_le_mul_right (2*Δ) hb
      nlinarith
end LowRankCounting

-- Source: Solutions.LowRankCertificates
open RGMISFast
namespace LowRankCounting
open Classical RGMISGeneral.Polynomial
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma root_mission {G : SimpleGraph V} {u : V} {A : Finset V} (h : IsRootConnected G u A) : RootConnected G u A := by
  refine ⟨h.1,?_⟩
  intro v hv
  have hp := (SimpleGraph.reachable_iff_reflTransGen (G:=restrictTo G (↑A)) u v).mp (h.2 v hv)
  clear hv
  induction hp with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨hs.1,hs.2.2⟩
lemma gamma_low_rank (G : SimpleGraph V) (r : V→ℝ) (Δ : ℕ) (A : Finset V)
    (v : V) (hv : v∈GammaLow G r Δ A) : r v<am (Mof Δ) := by
  obtain ⟨hvA,x,hx,hp⟩ := Finset.mem_filter.mp hv |>.2
  have hp' := (SimpleGraph.reachable_iff_reflTransGen ..).mp hp
  rcases hp'.cases_tail with he | ⟨y,hy,hs⟩
  · subst v; exact (hvA hx).elim
  · exact hs.2.2.resolve_left hvA
lemma gamma_attached (G : SimpleGraph V) (r : V→ℝ) (Δ : ℕ) (A : Finset V) :
    Attached G A (GammaLow G r Δ A) := by
  refine ⟨Finset.disjoint_left.mpr (fun v hv hg=> (Finset.mem_filter.mp hg).2.1 hv),?_⟩
  intro v hv
  obtain ⟨hvA,x,hx,hp⟩ := Finset.mem_filter.mp hv |>.2
  refine ⟨x,hx,?_⟩
  have hp' := (SimpleGraph.reachable_iff_reflTransGen ..).mp hp
  clear hv hvA hp
  induction hp' with
  | refl => exact .refl
  | @tail y z hp hs ih =>
    apply ih.tail
    refine ⟨hs.1,?_⟩
    by_cases hz : z∈A
    · exact Finset.mem_union_left _ hz
    · apply Finset.mem_union_right
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _,hz,x,hx,?_⟩
      exact (SimpleGraph.reachable_iff_reflTransGen ..).mpr (hp.tail hs)
lemma union_attached {G : SimpleGraph V} {u : V} {A T : Finset V}
    (hA : RootConnected G u A) (hT : Attached G A T) : RootConnected G u (A ∪ T) := by
  have lift (a : V) (ha : a∈A) : Relation.ReflTransGen (stepWithin G (A ∪ T)) u a :=
    Relation.ReflTransGen.mono (fun _ _ h=>⟨h.1,Finset.mem_union_left _ h.2⟩) _ _ (hA.2 a ha)
  refine ⟨Finset.mem_union_left _ hA.1,?_⟩
  intro v hv
  rcases Finset.mem_union.mp hv with hvA | hvT
  · exact lift v hvA
  · obtain ⟨a,ha,hp⟩ := hT.2 v hvT
    exact (lift a ha).trans hp
noncomputable def candidates (G : SimpleGraph V) (u : V) (j k : ℕ) : Finset (Finset V×Finset V) :=
  (sets G u (j+k)).biUnion (fun U=>((U.erase u).powersetCard k).image (fun T=>(U,T)))
lemma mem_candidates {G : SimpleGraph V} {u : V} {j k : ℕ} {U T : Finset V} :
    (U,T)∈candidates G u j k ↔ RootConnected G u U ∧ U.card=j+k+1 ∧ T⊆U.erase u ∧ T.card=k := by
  simp only [candidates,Finset.mem_biUnion,Finset.mem_image,Prod.mk.injEq,mem_sets,Finset.mem_powersetCard]
  constructor
  · rintro ⟨W,⟨hW,hc⟩,S,⟨hS,hSc⟩,rfl,rfl⟩; exact ⟨hW,hc,hS,hSc⟩
  · rintro ⟨hU,hc,hT,hTc⟩; exact ⟨U,⟨hU,hc⟩,T,⟨hT,hTc⟩,rfl,rfl⟩
lemma certificate {G : SimpleGraph V} {u : V} {r : V→ℝ} {Δ j k : ℕ} {A : Finset V}
    (hA : IsRootConnected G u A) (hc : A.card=j+1) (hk : k ≤ (GammaLow G r Δ A).card) :
    ∃UT∈candidates G u j k, ∀v∈UT.2,r v<am (Mof Δ) := by
  obtain ⟨T,hTsub,hT,hTc⟩ := exists_attached_subset_card (gamma_attached G r Δ A) k hk
  refine ⟨(A∪T,T),mem_candidates.mpr ⟨union_attached (root_mission hA) hT,?_,?_,hTc⟩,?_⟩
  · rw [Finset.card_union_of_disjoint hT.1,hc,hTc]; omega
  · intro v hv
    apply Finset.mem_erase.mpr
    refine ⟨?_,Finset.mem_union_right _ hv⟩
    intro he; subst v
    exact Finset.disjoint_left.mp hT.1 hA.1 hv
  · intro v hv
    exact gamma_low_rank G r Δ A v (hTsub hv)
lemma candidates_bound (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (j k Δ : ℕ)
    (hΔ : 2 ≤ Δ) (hd : ∀v,G.degree v ≤ Δ) : (candidates G u j k).card ≤ (8*Δ)^(j+k) := by
  calc
    _ ≤ ∑U∈sets G u (j+k),(((U.erase u).powersetCard k).image (fun T=>(U,T))).card := Finset.card_biUnion_le
    _ ≤ ∑_U∈sets G u (j+k),2^(j+k) := by
      apply Finset.sum_le_sum
      intro U hU
      have hmem := (mem_sets G u (j+k) U).mp hU
      have hc : (U.erase u).card=j+k := by rw [Finset.card_erase_of_mem hmem.1.1,hmem.2]; omega
      calc
        _ ≤ ((U.erase u).powersetCard k).card := Finset.card_image_le
        _ ≤ ((U.erase u).powerset).card := Finset.card_le_card (fun _ h=>Finset.mem_powerset.mpr (Finset.mem_powersetCard.mp h).1)
        _ = _ := by rw [Finset.card_powerset,hc]
    _ = (sets G u (j+k)).card*2^(j+k) := by simp
    _ ≤ (4*Δ)^(j+k)*2^(j+k) := Nat.mul_le_mul_right _ (count_bound G u (j+k) Δ hΔ hd)
    _ = _ := by rw [← mul_pow]; congr 1; omega
end LowRankCounting

-- Source: Solutions.ExponentialArrivals
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators
namespace ExponentialArrivals
open Classical
instance expOne_probability : IsProbabilityMeasure (expMeasure 1) :=
  isProbabilityMeasure_expMeasure (by norm_num)
instance expOne_nullSingleton : NullSingletonClass (expMeasure 1) := by
  unfold expMeasure gammaMeasure
  infer_instance

lemma expOne_real_Iio (s : ℝ) (hs : 0 ≤ s) :
    (expMeasure 1).real (Set.Iio s) = 1 - Real.exp (-s) := by
  rw [measureReal_def, measure_congr Iio_ae_eq_Iic, ← measureReal_def,
    ← cdf_eq_real, cdf_expMeasure_eq (by norm_num), if_pos hs]
  simp only [one_mul]
lemma expOne_real_Ici (s : ℝ) (hs : 0 ≤ s) :
    (expMeasure 1).real (Set.Ici s) = Real.exp (-s) := by
  rw [← Set.compl_Iio, probReal_compl_eq_one_sub measurableSet_Iio, expOne_real_Iio s hs]
  ring

variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def retainedVertices (S : Finset V) (s : ℝ) (r : V → ℝ) : Finset V :=
  S.filter (fun v => r v < s)
omit [DecidableEq V] in
theorem measurableSet_retainedVertices_eq (S T : Finset V) (b : ℝ) :
    MeasurableSet {u : V → ℝ | retainedVertices S b u = T} := by
  have heq : {u : V → ℝ | retainedVertices S b u = T} =
      {u : V → ℝ | ∀ v, (v ∈ S ∧ u v < b) ↔ v ∈ T} := by
    ext u
    simp [Finset.ext_iff, retainedVertices]
  rw [heq]
  apply Measurable.setOf
  apply Measurable.forall
  intro v
  exact (measurable_const.and ((measurable_pi_apply v).lt measurable_const)).iff
    measurable_const

omit [Fintype V] [DecidableEq V] in
theorem measurable_retainedVertices_card (S : Finset V) (b : ℝ) :
    Measurable (fun u : V → ℝ => (retainedVertices S b u).card) := by
  have heq : (fun u : V → ℝ => (retainedVertices S b u).card) =
      fun u => ∑ v ∈ S, if u v < b then (1 : ℕ) else 0 := by
    funext u
    simp only [retainedVertices, Finset.card_filter]
  rw [heq]
  apply Finset.measurable_sum
  intro v _
  exact Measurable.ite ((measurable_pi_apply v).lt measurable_const).setOf
    measurable_const measurable_const

omit [Fintype V] in
theorem retainedVertices_eq_pi (S T : Finset V) (hTS : T ⊆ S) (b : ℝ) :
    {u : V → ℝ | retainedVertices S b u = T} =
      (S : Set V).pi (fun v => if v ∈ T then Set.Iio b else Set.Ici b) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.mem_coe]
  constructor
  · intro heq v hv
    by_cases hvT : v ∈ T
    · have hmem : v ∈ retainedVertices S b u := heq.symm ▸ hvT
      simpa [hvT] using (Finset.mem_filter.mp hmem).2
    · simp only [hvT, ↓reduceIte, Set.mem_Ici]
      by_contra h
      exact hvT (heq ▸ Finset.mem_filter.mpr ⟨hv, lt_of_not_ge h⟩)
  · intro h
    apply Finset.ext
    intro v
    simp only [retainedVertices, Finset.mem_filter]
    constructor
    · rintro ⟨hvS, hvb⟩
      by_contra hvT
      have hge : b ≤ u v := by simpa [hvT] using h v hvS
      exact (not_lt_of_ge hge) hvb
    · intro hvT
      exact ⟨hTS hvT, by simpa [hvT] using h v (hTS hvT)⟩


theorem measure_retainedVertices_eq (S T : Finset V) (hTS : T ⊆ S)
    (s : ℝ) (hs : 0 ≤ s) :
    Measure.pi (fun _ : V => expMeasure 1) {u | retainedVertices S s u = T} =
      ENNReal.ofReal (1 - Real.exp (-s)) ^ T.card *
        ENNReal.ofReal (Real.exp (-s)) ^ (S.card - T.card) := by
  rw [retainedVertices_eq_pi S T hTS s, Measure.pi_pi_finset]
  have hlo : expMeasure 1 (Set.Iio s) = ENNReal.ofReal (1 - Real.exp (-s)) := by
    rw [← ofReal_measureReal, expOne_real_Iio s hs]
  have hhi : expMeasure 1 (Set.Ici s) = ENNReal.ofReal (Real.exp (-s)) := by
    rw [← ofReal_measureReal, expOne_real_Ici s hs]
  simp only [apply_ite,hlo,hhi]
  rw [Finset.prod_ite]
  have hfilter : S.filter (fun v => v ∈ T) = T := by
    ext v
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun hv => ⟨hTS hv,hv⟩⟩
  rw [hfilter, ← Finset.sdiff_eq_filter]
  simp [Finset.card_sdiff,Finset.inter_eq_left.mpr hTS]

theorem measureReal_retainedVertices_eq (S T : Finset V) (hTS : T ⊆ S)
    (s : ℝ) (hs : 0 ≤ s) :
    (Measure.pi (fun _ : V => expMeasure 1)).real {u | retainedVertices S s u = T} =
      (1 - Real.exp (-s)) ^ T.card * Real.exp (-s) ^ (S.card - T.card) := by
  have hp : 0 ≤ 1 - Real.exp (-s) := sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))
  rw [measureReal_def,measure_retainedVertices_eq S T hTS s hs,
    ENNReal.toReal_mul,ENNReal.toReal_pow,ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hp,ENNReal.toReal_ofReal (Real.exp_pos _).le]
/-- The cardinality of the retained set has the binomial distribution. -/
theorem measureReal_retainedVertices_card (S : Finset V) (j : ℕ)
    (b : ℝ) (hb : 0 ≤ b) :
    (Measure.pi (fun _ : V => expMeasure 1)).real
      {u | (retainedVertices S b u).card = j} =
      (S.card.choose j : ℝ) * (1 - Real.exp (-b)) ^ j *
        Real.exp (-b) ^ (S.card - j) := by
  have heq : {u : V → ℝ | (retainedVertices S b u).card = j} =
      ⋃ T ∈ S.powersetCard j, {u | retainedVertices S b u = T} := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, Finset.mem_powersetCard]
    constructor
    · intro hcard
      exact ⟨retainedVertices S b u, ⟨Finset.filter_subset _ _, hcard⟩, rfl⟩
    · rintro ⟨T, ⟨_, hT⟩, hEq⟩
      simpa [hEq] using hT
  rw [heq, measureReal_biUnion_finset]
  · calc
      _ = ∑ _T ∈ S.powersetCard j,
          (1 - Real.exp (-b)) ^ j *
            Real.exp (-b) ^ (S.card - j) := by
        apply Finset.sum_congr rfl
        intro T hT
        rcases Finset.mem_powersetCard.mp hT with ⟨hTS, hcard⟩
        rw [measureReal_retainedVertices_eq S T hTS b hb, hcard]
      _ = _ := by simp [mul_assoc]
  · intro T _ U _ hTU
    apply Set.disjoint_left.mpr
    intro u huT huU
    exact hTU (huT.symm.trans huU)
  · intro T _
    exact measurableSet_retainedVertices_eq S T b


end ExponentialArrivals

-- Source: Solutions.ConditionalRankBand
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
namespace ConditionalRankBand
open Classical ExponentialArrivals
variable {V : Type*} [Fintype V] [LinearOrder V]
noncomputable def marginal (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (rA : V → ℝ) (v : V) : Measure ℝ :=
  if r₀ v < θ then Measure.dirac (r₀ v) else if v∈A then Measure.dirac (rA v)
  else (expMeasure 1).map (fun x => θ+x)
instance marginal_probability (r₀ : V → ℝ) (θ : ℝ) (A : Finset V) (rA : V → ℝ) (v : V) :
    IsProbabilityMeasure (marginal r₀ θ A rA v) := by
  unfold marginal
  split_ifs
  · infer_instance
  · infer_instance
  · exact Measure.isProbabilityMeasure_map (by fun_prop)
def band (a : ℝ) (b : WithTop ℝ) : Set ℝ := {x | a ≤ x ∧ (x:WithTop ℝ)<b}
lemma band_measurable (a : ℝ) (b : WithTop ℝ) : MeasurableSet (band a b) := by
  induction b using WithTop.recTopCoe with
  | top =>
    convert (measurableSet_Ici : MeasurableSet (Set.Ici a)) using 1
    ext x; simp only [band,Set.mem_setOf_eq,WithTop.coe_lt_top, and_true,Set.mem_Ici]
  | coe b =>
    convert (measurableSet_Ico : MeasurableSet (Set.Ico a b)) using 1
    ext x; simp only [band,Set.mem_setOf_eq,WithTop.coe_lt_coe,Set.mem_Ico]
lemma exp_tail (s : ℝ) (hs : 0 ≤ s) : expMeasure 1 (Set.Ici s) = ENNReal.ofReal (Real.exp (-s)) := by
  rw [← ofReal_measureReal,expOne_real_Ici s hs]
lemma exp_band (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    expMeasure 1 (Set.Ico s t) = ENNReal.ofReal (1-Real.exp (-(t-s))) * expMeasure 1 (Set.Ici s) := by
  have hdiff : Set.Ici s \ Set.Ici t = Set.Ico s t := by ext x; simp
  rw [← hdiff,measure_sdiff (Set.Ici_subset_Ici.mpr hst) measurableSet_Ici.nullMeasurableSet (measure_ne_top _ _),
    exp_tail s hs,exp_tail t (hs.trans hst),← ENNReal.ofReal_sub _ (Real.exp_pos _).le,
    ← ENNReal.ofReal_mul (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith)))]
  congr 1
  rw [sub_mul,one_mul,←Real.exp_add]
  congr 2
  ring
lemma marginal_band (r₀ : V → ℝ) (θ a : ℝ) (hθa : θ < a) (A : Finset V) (rA : V → ℝ)
    (v : V) (hv : v∉A) (b : WithTop ℝ) (hab : (a:WithTop ℝ)<b) :
    marginal r₀ θ A rA v (band a b) =
      ENNReal.ofReal (oneMinusExp a b) * marginal r₀ θ A rA v (Set.Ici a) := by
  by_cases he : r₀ v < θ
  · have hr : r₀ v < a := he.trans hθa
    simp [marginal,he,band,not_le.mpr hr]
  · simp only [marginal,if_neg he,if_neg hv]
    rw [Measure.map_apply (by fun_prop) (band_measurable a b),Measure.map_apply (by fun_prop) measurableSet_Ici]
    have ht : (fun x : ℝ => θ+x) ⁻¹' Set.Ici a = Set.Ici (a-θ) := by
      ext x
      simp only [Set.mem_preimage,Set.mem_Ici]
      constructor <;> intro h <;> linarith
    rw [ht]
    induction b using WithTop.recTopCoe with
    | top =>
      simp only [band,WithTop.coe_lt_top,and_true,oneMinusExp,↓reduceDIte,ENNReal.ofReal_one,one_mul]
      congr 1
    | coe b =>
      have hb : a < b := WithTop.coe_lt_coe.mp hab
      have hi : (fun x : ℝ => θ+x) ⁻¹' band a (b:WithTop ℝ) = Set.Ico (a-θ) (b-θ) := by
        ext x
        simp only [Set.mem_preimage,band,Set.mem_setOf_eq,WithTop.coe_lt_coe,Set.mem_Ico]
        constructor <;> rintro ⟨h1,h2⟩ <;> constructor <;> linarith
      rw [hi,exp_band (a-θ) (b-θ) (by linarith) (by linarith)]
      simp only [oneMinusExp,WithTop.coe_ne_top,↓reduceDIte,WithTop.untop_coe]
      rw [show b-θ-(a-θ) = b-a by ring]
end ConditionalRankBand

-- Source: Solutions.EntriesGrowthSummation
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

lemma entries_band_factor_gt_one : 1 < c := by
  unfold c
  have h : 0 < 1/(2*Real.exp 2) := by positivity
  linarith

lemma entries_am_pos (n : ℕ) : 0 < am n := by
  have hc : 0 < c := lt_trans (by norm_num) entries_band_factor_gt_one
  unfold am a0
  positivity

lemma entries_am_step (n : ℕ) : am n = c*am (n+1) := by
  have hc : c ≠ 0 := (lt_trans (by norm_num) entries_band_factor_gt_one).ne'
  unfold am
  rw [pow_succ]
  field_simp

lemma entries_weighted_band_sum (N : ℕ) :
    (∑n∈Finset.range N, ((n:ℝ)+2)*am (n+1)) ≤ 4*(Real.exp 2)^3+4*(Real.exp 2)^2 := by
  have hc := entries_band_factor_gt_one
  have hden : 0 < (c-1)^2 := sq_pos_of_pos (by linarith)
  have hid : ∀N:ℕ, (c-1)^2*(∑n∈Finset.range N, ((n:ℝ)+2)*am (n+1))+
      am N*(((N:ℝ)+2)*c-((N:ℝ)+1)) = a0*(2*c-1) := by
    intro N
    induction N with
    | zero => simp [am]
    | succ N ih =>
      rw [Finset.sum_range_succ]
      push_cast
      rw [entries_am_step N] at ih
      nlinarith only [ih]
  have htail : 0 ≤ am N*(((N:ℝ)+2)*c-((N:ℝ)+1)) := by
    apply mul_nonneg (entries_am_pos N).le
    have hm := mul_le_mul_of_nonneg_left hc.le (show 0 ≤ (N:ℝ)+2 by positivity)
    linarith
  have hsum : (∑n∈Finset.range N, ((n:ℝ)+2)*am (n+1)) ≤ a0*(2*c-1)/(c-1)^2 := by
    apply (le_div_iff₀ hden).mpr
    nlinarith only [hid N,htail]
  have he : a0*(2*c-1)/(c-1)^2 = 4*(Real.exp 2)^3+4*(Real.exp 2)^2 := by
    unfold a0 c
    have hp : Real.exp 2 ≠ 0 := Real.exp_ne_zero 2
    field_simp
    ring
  exact hsum.trans_eq he

lemma entries_total_budget (N : ℕ) (L : ℝ) :
    (∑n∈Finset.range N, ((n:ℝ)+2)*(Real.exp (-2)+2*Real.exp (-4))*am (n+1)*Real.exp (-L)) ≤
      320*Real.exp (-L) := by
  have hcoef : 0 ≤ Real.exp (-2)+2*Real.exp (-4) := by positivity
  have hs := mul_le_mul_of_nonneg_left (entries_weighted_band_sum N)
    (mul_nonneg hcoef (Real.exp_pos (-L)).le)
  have hsum : (∑n∈Finset.range N, ((n:ℝ)+2)*(Real.exp (-2)+2*Real.exp (-4))*am (n+1)*Real.exp (-L)) =
      ((Real.exp (-2)+2*Real.exp (-4))*Real.exp (-L)) *
        (∑n∈Finset.range N, ((n:ℝ)+2)*am (n+1)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn; ring
  rw [hsum]
  have hfour : Real.exp (-4) = ((Real.exp 2)^2)⁻¹ := by
    rw [Real.exp_neg, ← Real.exp_nat_mul]
    norm_num
  have heq : (Real.exp (-2)+2*Real.exp (-4))*(4*(Real.exp 2)^3+4*(Real.exp 2)^2) =
      4*(Real.exp 2+1)*(Real.exp 2+2) := by
    rw [hfour,Real.exp_neg]
    have hp : Real.exp 2 ≠ 0 := Real.exp_ne_zero 2
    field_simp
  have he2 : Real.exp 2 ≤ (37/5:ℝ) := by
    have he1 := Real.exp_one_lt_d9
    have hepos := Real.exp_pos 1
    have he : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [←Real.exp_add]; norm_num
    rw [he]; nlinarith
  have hnum : 4*(Real.exp 2+1)*(Real.exp 2+2) ≤ 320 := by
    have hm := mul_le_mul (show Real.exp 2+1 ≤ (42/5:ℝ) by linarith)
      (show Real.exp 2+2 ≤ (47/5:ℝ) by linarith)
      (by positivity : 0 ≤ Real.exp 2+2) (by norm_num : (0:ℝ) ≤ 42/5)
    nlinarith
  have hm := mul_le_mul_of_nonneg_right hnum (Real.exp_pos (-L)).le
  have heq' := congrArg (fun x:ℝ => x*Real.exp (-L)) heq
  nlinarith only [hs,hm,heq']

-- Source: Solutions.LowRankProbability
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
namespace LowRankCounting
open Classical ExponentialArrivals
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma cutoff (Δ : ℕ) (hΔ : 2 ≤ Δ) : am (Mof Δ) ≤ 1/(16*(Δ:ℝ)) := by
  have hd : 0 < (Δ:ℝ) := by exact_mod_cast (by omega : 0<Δ)
  have hc := entries_band_factor_gt_one
  have hnonempty : {m : ℕ|am m ≤ 1/(16*(Δ:ℝ))}.Nonempty := by
    obtain ⟨n,hn⟩ := exists_nat_gt (a0*(16*(Δ:ℝ))/(c-1))
    have hm := (div_lt_iff₀ (show 0<c-1 by linarith)).mp hn
    have hb := one_add_mul_le_pow (show (-2:ℝ) ≤ c-1 by linarith) n
    rw [show 1+(c-1)=c by ring] at hb
    have hn : a0*(16*(Δ:ℝ)) < c^n := by linarith
    refine ⟨n,?_⟩
    change a0*(c^n)⁻¹ ≤ _
    rw [← div_eq_mul_inv,div_le_div_iff₀ (pow_pos (by linarith) _) (by positivity)]
    simpa using hn.le
  exact Nat.sInf_mem hnonempty
lemma low_coordinate (a : ℝ) (ha : 0 ≤ a) : expMeasure 1 (Set.Iio a) ≤ ENNReal.ofReal a := by
  rw [← Set.compl_Ici,measure_compl measurableSet_Ici (measure_ne_top _ _),measure_univ,
    ConditionalRankBand.exp_tail a ha]
  rw [← ENNReal.ofReal_one,← ENNReal.ofReal_sub _ (Real.exp_pos _).le]
  apply ENNReal.ofReal_le_ofReal
  linarith [Real.add_one_le_exp (-a)]
lemma low_set (T : Finset V) (a : ℝ) (ha : 0 ≤ a) :
    rankLaw V {r|∀v∈T,r v<a} ≤ ENNReal.ofReal a^T.card := by
  change Measure.pi (fun _ : V=>expMeasure 1) _ ≤ _
  have he : {r : V→ℝ|∀v∈T,r v<a} = (T:Set V).pi (fun _=>Set.Iio a) := by ext r; simp
  rw [he,Measure.pi_pi_finset]
  calc
    _ ≤ ∏_v∈T,ENNReal.ofReal a := Finset.prod_le_prod' (fun _ _=>low_coordinate a ha)
    _ = _ := by simp
end LowRankCounting

-- Source: Solutions.LowRankFixedSizeComplete
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
open Classical LowRankCounting
set_option maxHeartbeats 1000000

theorem low_rank_fixed_size_tail_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (hdeg : ∀v,G.degree v ≤ Δ) (u : V) (j k : ℕ) (hk : 1 ≤ k) :
    rankLaw V {r|∃A : Finset V,IsRootConnected G u A ∧ A.card=j+1 ∧
      k ≤ (GammaLow G r Δ A).card} ≤ ENNReal.ofReal ((8*(Δ:ℝ))^j*(1/2:ℝ)^k) := by
  let E : Finset V→Set (V→ℝ) := fun T=>{r|∀v∈T,r v<am (Mof Δ)}
  have hsub : {r|∃A : Finset V,IsRootConnected G u A ∧ A.card=j+1 ∧ k ≤ (GammaLow G r Δ A).card} ⊆
      ⋃UT∈candidates G u j k,E UT.2 := by
    rintro r ⟨A,hA,hc,hk⟩
    obtain ⟨UT,hUT,hr⟩ := certificate hA hc hk
    exact Set.mem_iUnion.mpr ⟨UT,Set.mem_iUnion.mpr ⟨hUT,hr⟩⟩
  have hd : 0 < (Δ:ℝ) := by exact_mod_cast (by omega : 0<Δ)
  have hE (UT : Finset V×Finset V) (hUT : UT∈candidates G u j k) :
      rankLaw V (E UT.2) ≤ ENNReal.ofReal ((1/(16*(Δ:ℝ)))^k) := by
    have hc := (mem_candidates.mp hUT).2.2.2
    calc
      _ ≤ ENNReal.ofReal (am (Mof Δ))^UT.2.card := low_set _ _ (entries_am_pos _).le
      _ ≤ ENNReal.ofReal (1/(16*(Δ:ℝ)))^k := by rw [hc]; gcongr; exact cutoff Δ hΔ
      _ = _ := (ENNReal.ofReal_pow (by positivity) k).symm
  calc
    _ ≤ rankLaw V (⋃UT∈candidates G u j k,E UT.2) := measure_mono hsub
    _ ≤ ∑UT∈candidates G u j k,rankLaw V (E UT.2) := measure_biUnion_finset_le _ _
    _ ≤ ∑_UT∈candidates G u j k,ENNReal.ofReal ((1/(16*(Δ:ℝ)))^k) := Finset.sum_le_sum hE
    _ = (candidates G u j k).card*ENNReal.ofReal ((1/(16*(Δ:ℝ)))^k) := by simp
    _ ≤ ((8*Δ)^(j+k):ℕ)*ENNReal.ofReal ((1/(16*(Δ:ℝ)))^k) := by
      exact mul_le_mul' (by exact_mod_cast candidates_bound G u j k Δ hΔ hdeg) le_rfl
    _ = _ := by
      rw [← ENNReal.ofReal_natCast,← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      push_cast
      rw [pow_add,mul_assoc,← mul_pow]
      have he : (8*(Δ:ℝ))*(1/(16*(Δ:ℝ))) = 1/2 := by field_simp; ring
      rw [he]

-- Source: Solutions.LowRankAllSizes
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
set_option autoImplicit false

lemma low_rank_exp_sum (L : ℝ) (n : ℕ) :
    (∑ j ∈ Finset.range n, Real.exp (-(j:ℝ)-L-2)) ≤ Real.exp (-L)/4 := by
  have he : (8/3:ℝ) ≤ Real.exp 1 := by linarith [Real.exp_one_gt_d9]
  have hq : Real.exp (-1) ≤ (2/5:ℝ) := by
    rw [Real.exp_neg]
    apply (inv_le_comm₀ (Real.exp_pos 1) (by norm_num)).mpr
    norm_num
    linarith
  have hsum : ∀ n, (∑j∈Finset.range n,Real.exp (-(j:ℝ))) ≤ (5/3:ℝ) := by
    intro n
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ']
      have hid : ∀j:ℕ,Real.exp (-((j+1:ℕ):ℝ)) = Real.exp (-1)*Real.exp (-(j:ℝ)) := by
        intro j; rw [← Real.exp_add]; congr 1; push_cast; ring
      simp_rw [hid]
      rw [← Finset.mul_sum]
      have hm := mul_le_mul_of_nonneg_left ih (Real.exp_pos (-1)).le
      norm_num
      nlinarith
  have hfactor : (∑j∈Finset.range n,Real.exp (-(j:ℝ)-L-2)) =
      Real.exp (-L-2)*(∑j∈Finset.range n,Real.exp (-(j:ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    rw [← Real.exp_add]
    congr 1; ring
  rw [hfactor]
  have hs := mul_le_mul_of_nonneg_left (hsum n) (Real.exp_pos (-L-2)).le
  have hexp : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
    rw [← Real.exp_add]; norm_num
  have he2 : (20/3:ℝ) ≤ Real.exp 2 := by rw [hexp]; nlinarith
  have hratio : Real.exp (-2)*(5/3:ℝ) ≤ 1/4 := by
    rw [Real.exp_neg]
    rw [inv_mul_eq_div]
    apply (div_le_iff₀ (Real.exp_pos 2)).mpr
    linarith
  have hid : Real.exp (-L-2) = Real.exp (-L)*Real.exp (-2) := by
    rw [← Real.exp_add]; congr 1
  rw [hid] at hs ⊢
  have hm := mul_le_mul_of_nonneg_left hratio (Real.exp_pos (-L)).le
  nlinarith

lemma low_rank_threshold_bound (Δ j : ℕ) (hΔ : 2 ≤ Δ) (L : ℝ) :
    (8*(Δ:ℝ))^j*(1/2:ℝ)^⌈((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2⌉₊ ≤
      Real.exp (-(j:ℝ)-L-2) := by
  have hd : 0 < (Δ:ℝ) := by exact_mod_cast (by omega : 0 < Δ)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb : 0 < 8*(Δ:ℝ) := by positivity
  have hbudget := (div_le_iff₀ hlog).mp (Nat.le_ceil
    (((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2))
  have hlogs : Real.log (8*Real.exp 1*Δ) = Real.log (8*(Δ:ℝ))+1 := by
    rw [show 8*Real.exp 1*(Δ:ℝ) = (8*(Δ:ℝ))*Real.exp 1 by ring,
      Real.log_mul (ne_of_gt hb) (Real.exp_ne_zero 1), Real.log_exp]
  have hid (k : ℕ) : (8*(Δ:ℝ))^j*(1/2:ℝ)^k =
      Real.exp ((j:ℝ)*Real.log (8*(Δ:ℝ))-(k:ℝ)*Real.log 2) := by
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log hb, Real.exp_log (by norm_num : (0:ℝ)<2)]
    simp [div_eq_mul_inv]
  rw [hid]
  apply Real.exp_le_exp.mpr
  rw [hlogs] at hbudget ⊢
  nlinarith

/-- The all-sizes argument, with the fixed-size probability estimate explicit. -/
theorem low_rank_all_sizes {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ)
    (u : V) (L : ℝ) (hL : 8 ≤ L)
    (hfixed : ∀j k:ℕ,1 ≤ k →
      rankLaw V {r | ∃A:Finset V, IsRootConnected G u A ∧ A.card=j+1 ∧
        k ≤ (GammaLow G r Δ A).card} ≤ ENNReal.ofReal ((8*(Δ:ℝ))^j*(1/2:ℝ)^k)) :
    rankLaw V {r | ¬ LowRankEvent G Δ u L r} ≤ ENNReal.ofReal (Real.exp (-L)/4) := by
  classical
  let k := fun j:ℕ => ⌈((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2⌉₊
  let E := fun j:ℕ => {r : V → ℝ | ∃A:Finset V, IsRootConnected G u A ∧ A.card=j+1 ∧
    k j ≤ (GammaLow G r Δ A).card}
  have hd : 2 ≤ (Δ:ℝ) := by exact_mod_cast hΔ
  have he : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hB : 1 ≤ 8*Real.exp 1*(Δ:ℝ) := by nlinarith
  have hlogB : 0 ≤ Real.log (8*Real.exp 1*Δ) := Real.log_nonneg hB
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hlog2pos : 0 < Real.log 2 := by linarith
  have hk : ∀j,1 ≤ k j := by
    intro j
    have hnum : 0 < (j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2 := by positivity
    have hp : 0 < ((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2 := div_pos hnum hlog2pos
    have hh := Nat.le_ceil (((j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2)/Real.log 2)
    have hn : 0 < (k j:ℝ) := lt_of_lt_of_le hp hh
    exact_mod_cast (show (1:ℕ) ≤ k j by exact Nat.succ_le_of_lt (by exact_mod_cast hn))
  have hsub : {r | ¬ LowRankEvent G Δ u L r} ⊆ ⋃j∈Finset.range (Fintype.card V),E j := by
    intro r hr
    change ¬ (∀A,IsRootConnected G u A → _) at hr
    push_neg at hr
    obtain ⟨A,hA,hbad⟩ := hr
    have hApos : 0 < A.card := Finset.card_pos.mpr ⟨u,hA.1⟩
    let j := A.card-1
    have hj : A.card = j+1 := by dsimp [j]; omega
    have hjbound : j < Fintype.card V := by have hh := Finset.card_le_univ A; omega
    refine Set.mem_iUnion.mpr ⟨j,Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hjbound,A,hA,hj,?_⟩⟩
    apply Nat.ceil_le.mpr
    apply (div_le_iff₀ hlog2pos).mpr
    have hnum : 0 ≤ (j:ℝ)*Real.log (8*Real.exp 1*Δ)+L+2 := by positivity
    have hcard : 0 ≤ ((GammaLow G r Δ A).card:ℝ) := Nat.cast_nonneg _
    have hmul := mul_le_mul_of_nonneg_left hlog2 hcard
    have hjreal : (A.card:ℝ) = (j:ℝ)+1 := by exact_mod_cast hj
    rw [hjreal] at hbad
    nlinarith
  have hE : ∀j,rankLaw V (E j) ≤ ENNReal.ofReal (Real.exp (-(j:ℝ)-L-2)) := by
    intro j
    exact (hfixed j (k j) (hk j)).trans (ENNReal.ofReal_le_ofReal (low_rank_threshold_bound Δ j hΔ L))
  calc
    _ ≤ rankLaw V (⋃j∈Finset.range (Fintype.card V),E j) := measure_mono hsub
    _ ≤ ∑j∈Finset.range (Fintype.card V),rankLaw V (E j) := measure_biUnion_finset_le _ _
    _ ≤ ∑j∈Finset.range (Fintype.card V),ENNReal.ofReal (Real.exp (-(j:ℝ)-L-2)) :=
      Finset.sum_le_sum (fun j _ => hE j)
    _ = ENNReal.ofReal (∑j∈Finset.range (Fintype.card V),Real.exp (-(j:ℝ)-L-2)) := by
      rw [ENNReal.ofReal_sum_of_nonneg (fun j _ => (Real.exp_pos _).le)]
    _ ≤ _ := ENNReal.ofReal_le_ofReal (low_rank_exp_sum L (Fintype.card V))

-- Source: Solutions.LemmaA1Complete
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal

theorem solution {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hΔ : 2 ≤ Δ) (hdeg : ∀v,G.degree v ≤ Δ) (u : V) (L : ℝ)
    (hL : 8 ≤ L) :
    rankLaw V {r|¬ LowRankEvent G Δ u L r} ≤ ENNReal.ofReal (Real.exp (-L)/4) := by
  exact low_rank_all_sizes G Δ hΔ u L hL (low_rank_fixed_size_tail_complete G Δ hΔ hdeg u)

#print axioms solution
