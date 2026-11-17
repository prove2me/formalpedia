-- Prove2me | solution 1 for RGMISFast.root_count_expectation_drift
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T05:58:01.739809+00:00
-- url     : https://prove2.me/submissions/9eeb110e-1d03-4833-891c-2f3353ee6bc3

import Definitions.Def_RGMISFast_Gamma
import Definitions.Def_RGMISFast_IsRootConnected
import Definitions.Def_RGMISFast_Y
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



-- Source: Solutions.CountMeasurability
open RGMISFast MeasureTheory
set_option autoImplicit false

lemma mis_true_iff {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (v : V) :
    inMIS G r v = true ↔ ∀ w, G.Adj v w → r w < r v → inMIS G r w = false := by
  rw [inMIS_eq]
  simp only [List.all_eq_true]
  constructor
  · intro h w ha hr
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using h ⟨w,(mem_lowerNbrs G r).mpr ⟨ha,hr⟩⟩ (by simp)
  · intro h w hw
    simpa only [Bool.not_eq_eq_eq_not, Bool.not_true] using h w.val ((mem_lowerNbrs G r).mp w.property).1 ((mem_lowerNbrs G r).mp w.property).2

lemma mis_order_congr {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r s : V → ℝ)
    (hord : ∀ v w, r v < r w ↔ s v < s w) (v : V) : inMIS G r v = inMIS G s v := by
  induction v using (measure (rk r)).wf.induction with
  | h v ih =>
    have he : inMIS G r v = true ↔ inMIS G s v = true := by
      rw [mis_true_iff,mis_true_iff]
      constructor
      · intro h w ha hw
        rw [← ih w (rk_lt r ((hord w v).mpr hw))]
        exact h w ha ((hord w v).mpr hw)
      · intro h w ha hw
        rw [ih w (rk_lt r hw)]
        exact h w ha ((hord w v).mp hw)
    cases hr : inMIS G r v <;> cases hs : inMIS G s v <;> simp_all

lemma mis_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    Measurable (fun r : V → ℝ => inMIS G r v) := by
  classical
  let code : (V → ℝ) → (V → V → Prop) := fun r a b => r a < r b
  have hm : Measurable code := by
    apply measurable_pi_lambda
    intro a
    apply measurable_pi_lambda
    intro b
    exact measurableSet_setOf.mp (measurableSet_lt (measurable_pi_apply a) (measurable_pi_apply b))
  have hf : (fun r : V → ℝ => inMIS G r v).FactorsThrough code := by
    intro r s he
    apply mis_order_congr G r s
    intro a b
    exact iff_of_eq (congrFun (congrFun he a) b)
  obtain ⟨f,he⟩ := (Function.factorsThrough_iff _).mp hf
  rw [he]
  exact (measurable_of_countable f).comp hm

lemma active_vertex_iff {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (t : ℝ) (v : V) :
    t ≤ tau G r v ↔ ∀ w, (w = v ∨ G.Adj v w) → inMIS G r w = true → t ≤ r w := by
  classical
  unfold tau
  rw [Finset.le_min'_iff]
  constructor
  · intro h w hw hm
    exact h (r w) (Finset.mem_image.mpr ⟨w,Finset.mem_filter.mpr
      ⟨by simpa using hw,hm⟩,rfl⟩)
  · intro h y hy
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨hw,hm⟩ := Finset.mem_filter.mp hw
    exact h w (by simpa using hw) hm

lemma active_vertex_measurable {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (v : V) :
    MeasurableSet {r : V → ℝ | t ≤ tau G r v} := by
  simp only [active_vertex_iff, Set.setOf_forall]
  apply MeasurableSet.iInter
  intro w
  apply MeasurableSet.iInter
  intro hw
  have hm := mis_measurable G w
  have hb : MeasurableSet {r : V → ℝ | inMIS G r w = true} := measurableSet_eq_fun hm measurable_const
  have ht : MeasurableSet {r : V → ℝ | t ≤ r w} := measurableSet_le measurable_const (measurable_pi_apply w)
  convert hb.compl.union ht using 1
  ext r
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_compl_iff, imp_iff_not_or]

lemma measurable_of_activity {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (f : (V → ℝ) → ℕ)
    (hf : ∀ r s, (∀ v, t ≤ tau G r v ↔ t ≤ tau G s v) → f r = f s) : Measurable f := by
  classical
  let code : (V → ℝ) → (V → Prop) := fun r v => t ≤ tau G r v
  have hm : Measurable code := by
    apply measurable_pi_lambda
    intro v
    exact measurableSet_setOf.mp (active_vertex_measurable G t v)
  have hfac : f.FactorsThrough code := by
    intro r s he
    exact hf r s (fun v => iff_of_eq (congrFun he v))
  obtain ⟨g,he⟩ := (Function.factorsThrough_iff _).mp hfac
  rw [he]
  exact (measurable_of_countable g).comp hm

lemma activeAt_congr {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℝ) (r s : V → ℝ)
    (h : ∀ v, t ≤ tau G r v ↔ t ≤ tau G s v) (A : Finset V) :
    ActiveAt G r t A = ActiveAt G s t A := by
  unfold ActiveAt
  simp_rw [h]

lemma Ncount_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => Ncount G A k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  unfold Ncount
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [activeAt_congr G t r s h]

lemma Y_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => Y G u k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  unfold Y
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [activeAt_congr G t r s h]

lemma dsSum_measurable_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) :
    Measurable (fun r : V → ℝ => dsSum G u k t r) := by
  classical
  apply measurable_of_activity G t
  intro r s h
  have he : {x | t ≤ tau G r x} = {x | t ≤ tau G s x} := Set.ext h
  have hc : countedW G u k t r = countedW G u k t s := by
    unfold countedW
    apply Finset.filter_congr
    intro W hw
    rw [activeAt_congr G t r s h]
  unfold dsSum
  rw [he,hc]

-- Source: Solutions.SingleArrival
open RGMISFast
namespace SingleArrival
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ)

/-- Across an interval with exactly one possible arriving vertex, only that
vertex's selection can change activity. -/
lemma activity_transition (s t : ℝ) (hst : s ≤ t) (x v : V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    t ≤ tau G r v ↔ s ≤ tau G r v ∧
      (inMIS G r x = true → v ≠ x ∧ ¬ G.Adj v x) := by
  constructor
  · intro ht
    refine ⟨hst.trans ht, ?_⟩
    intro hm
    have h := (active_vertex_iff G r t v).mp ht
    constructor
    · intro he
      subst v
      exact (not_le_of_gt hx.2) (h x (Or.inl rfl) hm)
    · intro ha
      exact (not_le_of_gt hx.2) (h x (Or.inr ha) hm)
  · rintro ⟨hs, hsafe⟩
    apply (active_vertex_iff G r t v).mpr
    intro w hw hm
    have hsw := (active_vertex_iff G r s v).mp hs w hw hm
    by_contra htw
    have hwx := hone w hsw (lt_of_not_ge htw)
    subst w
    rcases hw with he | ha
    · exact (hsafe hm).1 he.symm
    · exact (hsafe hm).2 ha

/-- The unique arrival is selected exactly when it is still active at the
start of the interval. -/
lemma arrival_selected_iff (s t : ℝ) (x : V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    inMIS G r x = true ↔ s ≤ tau G r x := by
  constructor
  · intro hm
    apply (active_vertex_iff G r s x).mpr
    intro w hw hwm
    rcases hw with he | ha
    · simpa only [he] using hx.1
    · by_contra hws
      have hl : r w < r x := (lt_of_not_ge hws).trans_le hx.1
      have hf := (mis_true_iff G r x).mp hm w ha hl
      simp_all
  · intro hs
    apply (mis_true_iff G r x).mpr
    intro w ha hw
    cases hm : inMIS G r w with
    | false => rfl
    | true =>
      have hsw := (active_vertex_iff G r s x).mp hs w (Or.inr ha) hm
      have he := hone w hsw (hw.trans hx.2)
      subst w
      exact False.elim (lt_irrefl _ hw)

lemma active_transition (s t : ℝ) (hst : s ≤ t) (x v : V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    t ≤ tau G r v ↔ s ≤ tau G r v ∧
      (s ≤ tau G r x → v ≠ x ∧ ¬ G.Adj v x) := by
  rw [activity_transition G r s t hst x v hx hone, ← arrival_selected_iff G r s t x hx hone]
end SingleArrival

namespace SingleArrival
variable {V : Type*} [Fintype V] [LinearOrder V]
variable (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ)
lemma active_set_transition (s t : ℝ) (hst : s ≤ t) (x : V) (A : Finset V)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    ActiveAt G r t A ↔ ActiveAt G r s A ∧
      (s ≤ tau G r x → ∀ v ∈ A, v ≠ x ∧ ¬ G.Adj v x) := by
  constructor
  · intro h
    constructor
    · intro v hv
      exact hst.trans (h v hv)
    · intro hxa v hv
      exact ((active_transition G r s t hst x v hx hone).mp (h v hv)).2 hxa
  · rintro ⟨h,hkeep⟩ v hv
    exact (active_transition G r s t hst x v hx hone).mpr ⟨h v hv,fun hxa => hkeep hxa v hv⟩
end SingleArrival

-- Source: Solutions.RootCountCorrespondence
open RGMISFast
set_option autoImplicit false

lemma singleton_attached_iff {V : Type*} [DecidableEq V] (G : SimpleGraph V) (u : V) (W : Finset V) :
    IsAttached G {u} W ↔ u ∉ W ∧ IsRootConnected G u (insert u W) := by
  classical
  constructor
  · rintro ⟨hd,hr⟩
    have hu : u ∉ W := by simpa using hd
    refine ⟨hu,Finset.mem_insert_self _ _,?_⟩
    intro x hx
    rcases Finset.mem_insert.mp hx with he | hx
    · subst x
      exact .refl _
    · obtain ⟨y,hy,hyx⟩ := hr x hx
      have he : y = u := Finset.mem_singleton.mp hy
      subst y
      simpa using hyx
  · rintro ⟨hu,hroot⟩
    refine ⟨by simpa using hu,?_⟩
    intro w hw
    exact ⟨u,Finset.mem_singleton_self _,by simpa using hroot.2 w (Finset.mem_insert_of_mem hw)⟩

lemma Y_eq_Ncount_singleton {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (t : ℝ) (r : V → ℝ) :
    Y G u k t r = Ncount G {u} k t r := by
  classical
  unfold Y Ncount
  symm
  apply Finset.card_bij (fun W _ => insert u W)
  · intro W hW
    obtain ⟨_,hc,ha,ht⟩ := Finset.mem_filter.mp hW
    obtain ⟨hu,hr⟩ := (singleton_attached_iff G u W).mp ha
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,hr,?_,by simpa using ht⟩
    rw [Finset.card_insert_of_notMem hu,hc]
  · intro W hW Z hZ he
    have huW := ((singleton_attached_iff G u W).mp (Finset.mem_filter.mp hW).2.2.1).1
    have huZ := ((singleton_attached_iff G u Z).mp (Finset.mem_filter.mp hZ).2.2.1).1
    have hh := congrArg (fun A : Finset V => A.erase u) he
    simpa [Finset.erase_insert,Finset.erase_eq_of_notMem huW,Finset.erase_eq_of_notMem huZ] using hh
  · intro B hB
    obtain ⟨_,hr,hcard,ht⟩ := Finset.mem_filter.mp hB
    have he : insert u (B.erase u) = B := Finset.insert_erase hr.1
    refine ⟨B.erase u,?_,he⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_,?_,?_⟩
    · rw [Finset.card_erase_of_mem hr.1,hcard]
      omega
    · apply (singleton_attached_iff G u _).mpr
      exact ⟨Finset.notMem_erase _ _,by simpa only [he] using hr⟩
    · simpa [he] using ht

-- Source: Solutions.ArrivalAuxiliary
open RGMISFast
namespace ArrivalAuxiliary
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma active_le_rank (G : SimpleGraph V) [DecidableRel G.Adj] (r : V → ℝ) (s : ℝ) (v : V)
    (hv : s ≤ tau G r v) : s ≤ r v := by
  by_contra hvs
  have hlt := lt_of_not_ge hvs
  have hm : inMIS G r v = true := by
    apply (mis_true_iff G r v).mpr
    intro w ha hw
    cases he : inMIS G r w with
    | false => rfl
    | true =>
      have hs := (active_vertex_iff G r s v).mp hv w (Or.inr ha) he
      exact False.elim ((not_le_of_gt (hw.trans hlt)) hs)
  exact (not_le_of_gt hlt) ((active_vertex_iff G r s v).mp hv v (Or.inl rfl) hm)
lemma activity_no_arrival (G : SimpleGraph V) [DecidableRel G.Adj]
    (r : V → ℝ) (s t : ℝ) (hst : s ≤ t)
    (hn : ∀ w, ¬ (s ≤ r w ∧ r w < t)) (v : V) :
    s ≤ tau G r v ↔ t ≤ tau G r v := by
  constructor
  · intro h
    apply (active_vertex_iff G r t v).mpr
    intro w hw hm
    have hs := (active_vertex_iff G r s v).mp h w hw hm
    exact le_of_not_gt (fun ht => hn w ⟨hs,ht⟩)
  · exact fun h => hst.trans h
lemma Y_eq_countedW (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) : Y G u k s r = (countedW G u k s r).card := by
  classical
  rw [Y_eq_Ncount_singleton]
  unfold Ncount countedW
  congr 1
  apply Finset.filter_congr
  intro W hw
  rw [singleton_attached_iff]
  simp only [Finset.singleton_union]
  tauto
end ArrivalAuxiliary

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

-- Source: Solutions.PermutationSymmetry
namespace ArrivalSymmetry
open MeasureTheory

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (μ : Measure ℝ) [IsProbabilityMeasure μ]

/-- Relabel independent rank coordinates by a finite permutation. -/
def coordinatePermutation (σ : Equiv.Perm V) : (V → ℝ) ≃ᵐ (V → ℝ) :=
  MeasurableEquiv.piCongrLeft (fun _ : V => ℝ) σ.symm

@[simp] theorem coordinatePermutation_apply (σ : Equiv.Perm V) (r : V → ℝ) (v : V) :
    coordinatePermutation σ r v = r (σ v) := by
  simp [coordinatePermutation, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply]

theorem coordinatePermutation_measurePreserving (σ : Equiv.Perm V) :
    MeasurePreserving (coordinatePermutation σ)
      (Measure.pi (fun _ : V => μ))
      (Measure.pi (fun _ : V => μ)) :=
  measurePreserving_piCongrLeft (fun _ : V => μ) σ.symm

theorem integral_coordinatePermutation (σ : Equiv.Perm V) (F : (V → ℝ) → ℝ) :
    (∫ r, F (coordinatePermutation σ r) ∂Measure.pi (fun _ => μ)) =
      ∫ r, F r ∂Measure.pi (fun _ => μ) :=
  (coordinatePermutation_measurePreserving μ σ).integral_comp
    (coordinatePermutation σ).measurableEmbedding F

/-- Pointwise uniform average over all coordinate permutations. -/
noncomputable def permutationAverage (F : (V → ℝ) → ℝ) (r : V → ℝ) : ℝ :=
  (∑ σ : Equiv.Perm V, F (coordinatePermutation σ r)) / Fintype.card (Equiv.Perm V)

theorem integral_permutationAverage (F : (V → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi (fun _ : V => μ))) :
    (∫ r, permutationAverage F r ∂Measure.pi (fun _ => μ)) =
      ∫ r, F r ∂Measure.pi (fun _ => μ) := by
  have hcomp (σ : Equiv.Perm V) :
      Integrable (fun r => F (coordinatePermutation σ r))
        (Measure.pi (fun _ : V => μ)) :=
    ((coordinatePermutation_measurePreserving μ σ).integrable_comp hF.aestronglyMeasurable).mpr hF
  unfold permutationAverage
  rw [integral_div, integral_finsetSum _ (fun σ _ => hcomp σ)]
  simp_rw [integral_coordinatePermutation μ]
  have hn : (Fintype.card (Equiv.Perm V) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact mul_div_cancel_left₀ _ hn

/-- Averaging over permutations may be replaced by an a.e. identified statistic. -/
theorem integral_eq_of_permutationAverage_ae (F H : (V → ℝ) → ℝ)
    (hF : Integrable F (Measure.pi (fun _ : V => μ)))
    (havg : permutationAverage F =ᵐ[Measure.pi (fun _ : V => μ)] H) :
    (∫ r, F r ∂Measure.pi (fun _ => μ)) =
      ∫ r, H r ∂Measure.pi (fun _ => μ) := by
  rw [← integral_permutationAverage μ F hF]
  exact integral_congr_ae havg

/-- Finite-range expectation written using the actual masses of its level sets. -/
theorem integral_comp_nat_bounded {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (K : Ω → ℕ) (hK : Measurable K)
    (n : ℕ) (hKn : ∀ ω, K ω ≤ n) (g : ℕ → ℝ) :
    (∫ ω, g (K ω) ∂μ) =
      ∑ j ∈ Finset.range (n + 1), μ.real {ω | K ω = j} * g j := by
  classical
  have heq (ω : Ω) : g (K ω) =
      ∑ j ∈ Finset.range (n + 1), if K ω = j then g j else 0 := by
    simp [eq_comm, Finset.mem_range.mpr (Nat.lt_succ_of_le (hKn ω))]
  have hmeas (j : ℕ) : MeasurableSet {ω | K ω = j} :=
    (hK.eq measurable_const).setOf
  have hf (j : ℕ) : (fun ω => if K ω = j then g j else 0) =
      ({ω | K ω = j}).indicator (fun _ => g j) := by
    funext ω
    simp [Set.indicator]
  have hint (j : ℕ) : Integrable (fun ω => if K ω = j then g j else 0) μ := by
    rw [hf]
    exact (integrable_const (μ := μ) (g j)).indicator (hmeas j)
  simp_rw [heq]
  rw [integral_finsetSum _ (fun j _ => hint j)]
  apply Finset.sum_congr rfl
  intro j _
  rw [hf]
  rw [integral_indicator (hmeas j), integral_const]
  simp [Measure.real, Measure.restrict_apply_univ, smul_eq_mul]


end ArrivalSymmetry

-- Source: Solutions.ArrivalOrder
open MeasureTheory ProbabilityTheory
namespace ArrivalOrder
open Classical ExponentialArrivals ArrivalSymmetry
/-- Number of raw coordinates strictly below a threshold. -/
noncomputable def rankArrivalCount {V : Type*} [Fintype V] (raw : V → ℝ) (t : ℝ) : ℕ :=
  (Finset.univ.filter fun v => raw v < t).card

theorem rankArrivalCount_le {V : Type*} [Fintype V] (raw : V → ℝ) (t : ℝ) :
    rankArrivalCount raw t ≤ Fintype.card V := Finset.card_le_univ _

/-- The increasing enumeration of an injective finite rank assignment. -/
noncomputable def sortedRankEquiv {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (hinj : Function.Injective raw) : Fin n ≃ V := by
  letI := LinearOrder.lift' raw hinj
  exact (Fintype.orderIsoFinOfCardEq V (by simpa using Fintype.card_congr e.symm)).toEquiv

theorem sortedRankEquiv_strictMono {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (hinj : Function.Injective raw) :
    StrictMono (fun i => raw (sortedRankEquiv e raw hinj i)) := by
  letI := LinearOrder.lift' raw hinj
  exact (Fintype.orderIsoFinOfCardEq V
    (by simpa using Fintype.card_congr e.symm)).strictMono

theorem rankArrivalCount_le_of_equiv {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (t : ℝ) : rankArrivalCount raw t ≤ n := by
  have hcard : Fintype.card V = n := by simpa using Fintype.card_congr e.symm
  simpa [hcard] using rankArrivalCount_le raw t

/-- In increasing rank order, precisely the first `rankArrivalCount` positions have arrived. -/
theorem sortedRankEquiv_lt_iff {V : Type*} [Fintype V] {n : ℕ}
    (e : Fin n ≃ V) (raw : V → ℝ) (hinj : Function.Injective raw) (t : ℝ) (i : Fin n) :
    i.val < rankArrivalCount raw t ↔ raw (sortedRankEquiv e raw hinj i) < t := by
  have hcard : (Finset.univ.filter fun j : Fin n =>
      raw (sortedRankEquiv e raw hinj j) < t).card = rankArrivalCount raw t := by
    apply Finset.card_equiv (sortedRankEquiv e raw hinj)
    intro j
    simp
  rw [← hcard]
  apply Fin.lt_card_filter_univ_iff_apply_of_imp
  intro a b hba ha
  exact ((sortedRankEquiv_strictMono e raw hinj).monotone hba).trans_lt ha


section
variable {V : Type*} [Fintype V]
theorem ae_rawRanks_distinct {v w : V} (hvw : v ≠ w) :
    ∀ᵐ r : V → ℝ ∂Measure.pi (fun _ => (expMeasure 1)), r v ≠ r w := by
  have hind : IndepFun (fun r : V → ℝ => r v) (fun r : V → ℝ => r w)
      (Measure.pi (fun _ => (expMeasure 1))) :=
    (iIndepFun_pi (μ := fun _ : V => (expMeasure 1))
      (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hvw
  have hmap := hind.map_prod_eq_prod_map_map
    (measurable_pi_apply v).aemeasurable (measurable_pi_apply w).aemeasurable
  rw [(measurePreserving_eval (fun _ : V => (expMeasure 1)) v).map_eq,
    (measurePreserving_eval (fun _ : V => (expMeasure 1)) w).map_eq] at hmap
  have hpair : ∀ᵐ z ∂(expMeasure 1).prod (expMeasure 1), z.1 ≠ z.2 := by
    rw [ae_iff]
    simp only [not_not]
    apply Measure.measure_prod_null_of_ae_null
    · exact measurableSet_eq_fun
        (measurable_fst : Measurable (fun z : ℝ × ℝ => z.1)) measurable_snd
    · filter_upwards [] with x
      change (expMeasure 1) {y : ℝ | x = y} = 0
      simp
  apply ae_of_ae_map (μ := Measure.pi (fun _ : V => (expMeasure 1)))
    (f := fun r : V → ℝ => (r v, r w)) (p := fun z : ℝ × ℝ => z.1 ≠ z.2)
    ((measurable_pi_apply v).prodMk (measurable_pi_apply w)).aemeasurable
  rw [hmap]
  exact hpair

theorem ae_rawRanks_injective :
    ∀ᵐ r : V → ℝ ∂Measure.pi (fun _ => (expMeasure 1)), Function.Injective r := by
  apply Filter.eventually_all.mpr
  intro v
  apply Filter.eventually_all.mpr
  intro w
  by_cases h : v = w
  · exact Filter.Eventually.of_forall (fun _ _ => h)
  · filter_upwards [ae_rawRanks_distinct h] with r hr heq
    exact (hr heq).elim


end
end ArrivalOrder

-- Source: Solutions.ArrivalPolynomial
namespace ArrivalPolynomial
open scoped BigOperators
open Set

noncomputable def arrivalWeight (n j : ℕ) (t : ℝ) : ℝ :=
  (bernsteinPolynomial ℝ n j).eval t

theorem arrivalWeight_formula (n j : ℕ) (t : ℝ) :
    arrivalWeight n j t = (n.choose j : ℝ) * t ^ j * (1 - t) ^ (n - j) := by
  simp [arrivalWeight, bernsteinPolynomial]

theorem arrivalWeight_nonneg (n j : ℕ) (t : ℝ) (ht : t ∈ Icc 0 1) :
    0 ≤ arrivalWeight n j t := by
  rw [arrivalWeight_formula]
  exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg ht.1 _))
    (pow_nonneg (sub_nonneg.mpr ht.2) _)

theorem arrivalWeight_sum (n : ℕ) (t : ℝ) :
    (∑ j ∈ Finset.range (n + 1), arrivalWeight n j t) = 1 := by
  have h := congrArg (fun p : Polynomial ℝ ↦ p.eval t) (bernsteinPolynomial.sum ℝ n)
  simpa [arrivalWeight, Polynomial.eval_finsetSum] using h

theorem arrivalWeight_eq_zero_of_lt (n j : ℕ) (t : ℝ) (h : n < j) :
    arrivalWeight n j t = 0 := by
  simp [arrivalWeight, bernsteinPolynomial.eq_zero_of_lt ℝ h]

theorem hasDerivAt_arrivalWeight_zero (n : ℕ) (t : ℝ) :
    HasDerivAt (arrivalWeight n 0) (-(n : ℝ) * arrivalWeight (n - 1) 0 t) t := by
  have h := (bernsteinPolynomial ℝ n 0).hasDerivAt t
  rw [bernsteinPolynomial.derivative_zero] at h
  convert! h using 1
  simp [arrivalWeight]

theorem hasDerivAt_arrivalWeight_succ (n j : ℕ) (t : ℝ) :
    HasDerivAt (arrivalWeight (n + 1) (j + 1))
      (((n : ℝ) + 1) * (arrivalWeight n j t - arrivalWeight n (j + 1) t)) t := by
  have h := (bernsteinPolynomial ℝ (n + 1) (j + 1)).hasDerivAt t
  rw [bernsteinPolynomial.derivative_succ_aux] at h
  convert! h using 1
  simp [arrivalWeight]

noncomputable def arrivalMixture (n : ℕ) (g : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (n + 1), arrivalWeight n j t * g j

/-- The derivative is the Bernstein mixture of successive differences. -/
theorem hasDerivAt_arrivalMixture_succ (n : ℕ) (g : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (arrivalMixture (n + 1) g)
      (((n : ℝ) + 1) *
        ∑ j ∈ Finset.range (n + 1), arrivalWeight n j t * (g (j + 1) - g j)) t := by
  have htail : HasDerivAt
      (fun t ↦ ∑ j ∈ Finset.range (n + 1), arrivalWeight (n + 1) (j + 1) t * g (j + 1))
      (∑ j ∈ Finset.range (n + 1),
        (((n : ℝ) + 1) * (arrivalWeight n j t - arrivalWeight n (j + 1) t)) * g (j + 1)) t := by
    convert! HasDerivAt.sum
      (fun j (_hj : j ∈ Finset.range (n + 1)) ↦
        (hasDerivAt_arrivalWeight_succ n j t).mul_const (g (j + 1))) using 1
    ext x
    simp only [Finset.sum_apply]
  have hhead := (hasDerivAt_arrivalWeight_zero (n + 1) t).mul_const (g 0)
  have htotal := htail.add hhead
  have hshift :
      (∑ j ∈ Finset.range (n + 1), arrivalWeight n (j + 1) t * g (j + 1)) +
        arrivalWeight n 0 t * g 0 =
      ∑ j ∈ Finset.range (n + 1), arrivalWeight n j t * g j := by
    rw [← Finset.sum_range_succ' (fun j ↦ arrivalWeight n j t * g j) (n + 1),
      Finset.sum_range_succ]
    rw [arrivalWeight_eq_zero_of_lt n (n + 1) t (Nat.lt_succ_self n)]
    ring
  convert! htotal using 1
  · ext x
    exact Finset.sum_range_succ' (fun j ↦ arrivalWeight (n + 1) j x * g j) (n + 1)
  · simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
    simp only [sub_mul, mul_sub, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
    have hm := congrArg (fun z : ℝ ↦ ((n : ℝ) + 1) * z) hshift
    nlinarith

/-- The change from `n-1` to `n` Bernstein weights is exactly the number of
unarrived coordinates times the remaining-time factor. -/
theorem arrivalWeight_step_identity (n j : ℕ) (t : ℝ) (hj : j ≤ n) :
    ((n + 1 - j : ℕ) : ℝ) * arrivalWeight (n + 1) j t =
      ((n : ℝ) + 1) * (1 - t) * arrivalWeight n j t := by
  have hchoose : ((n + 1 - j : ℕ) : ℝ) * ((n + 1).choose j : ℝ) =
      ((n : ℝ) + 1) * (n.choose j : ℝ) := by
    have h := congrArg (fun m : ℕ ↦ (m : ℝ)) (Nat.choose_mul_succ_eq n j)
    push_cast at h
    nlinarith [h]
  have hsub : n + 1 - j = (n - j) + 1 := by omega
  rw [arrivalWeight_formula, arrivalWeight_formula, hsub, pow_succ]
  calc
    _ = (((n - j + 1 : ℕ) : ℝ) * ((n + 1).choose j : ℝ)) *
        (t ^ j * (1 - t) ^ (n - j) * (1 - t)) := by ring
    _ = (((n : ℝ) + 1) * (n.choose j : ℝ)) *
        (t ^ j * (1 - t) ^ (n - j) * (1 - t)) := by rw [← hsub, hchoose]
    _ = _ := by ring

noncomputable def arrivalDrift (n : ℕ) (g : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range n, arrivalWeight n j t * ((n - j : ℕ) : ℝ) * (g j - g (j + 1))

/-- The actual derivative identity in arrival-hazard form. -/
theorem hasDerivAt_arrivalMixture (n : ℕ) (g : ℕ → ℝ) (t : ℝ)
    (hn : 0 < n) (ht : t ≠ 1) :
    HasDerivAt (arrivalMixture n g) (-arrivalDrift n g t / (1 - t)) t := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  convert! hasDerivAt_arrivalMixture_succ m g t using 1
  dsimp [arrivalDrift]
  rw [← Finset.sum_neg_distrib, Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  have hweight := arrivalWeight_step_identity m j t (by simp only [Finset.mem_range] at hj; omega)
  have htne : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  apply (div_eq_iff htne).mpr
  have hm := congrArg (fun z : ℝ ↦ z * (g j - g (j + 1))) hweight
  nlinarith [hm]


end ArrivalPolynomial

-- Source: Solutions.OrderMixture
open MeasureTheory ProbabilityTheory
namespace OrderMixture
open Classical ArrivalSymmetry ArrivalOrder ExponentialArrivals ArrivalPolynomial
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
noncomputable def representative (e : Fin n ≃ V) (σ : Equiv.Perm V) : V → ℝ :=
  fun v => ((e.symm (σ v)).val : ℝ)
noncomputable def profile (e : Fin n ≃ V) (H : ℝ → (V → ℝ) → ℝ) (j : ℕ) : ℝ :=
  (∑ σ : Equiv.Perm V, H (j : ℝ) (representative e σ)) / Fintype.card (Equiv.Perm V)

def PrefixInvariant (H : ℝ → (V → ℝ) → ℝ) : Prop :=
  ∀ r q s t,
    (∀ v, r v < s ↔ q v < t) →
    (∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) →
    H s r = H t q

theorem permutation_average_eq_profile (e : Fin n ≃ V)
    (H : ℝ → (V → ℝ) → ℝ) (hH : PrefixInvariant H)
    (r : V → ℝ) (hr : Function.Injective r) (s : ℝ) :
    permutationAverage (H s) r = profile e H (rankArrivalCount r s) := by
  let q := sortedRankEquiv e r hr
  let K : Equiv.Perm V := q.symm.trans e
  have hv (σ : Equiv.Perm V) : H s (coordinatePermutation σ r) =
      H (rankArrivalCount r s : ℝ) (representative e (K * σ)) := by
    apply hH
    · intro v
      have hi : e.symm ((K * σ) v) = q.symm (σ v) := by
        simp [K,Equiv.Perm.mul_apply]
      simp only [coordinatePermutation_apply,representative,hi]
      have h := sortedRankEquiv_lt_iff e r hr s (q.symm (σ v))
      have he : sortedRankEquiv e r hr (q.symm (σ v)) = σ v := q.apply_symm_apply _
      rw [he] at h
      exact h.symm.trans (by simp)
    · intro v w hv hw
      have hi (v : V) : e.symm ((K * σ) v) = q.symm (σ v) := by
        simp [K,Equiv.Perm.mul_apply]
      simp only [coordinatePermutation_apply,representative,hi]
      have hmono : StrictMono (fun i => r (q i)) := sortedRankEquiv_strictMono e r hr
      have hh := hmono.lt_iff_lt (a := q.symm (σ v)) (b := q.symm (σ w))
      simpa only [Equiv.apply_symm_apply,Fin.lt_def,Nat.cast_lt] using hh
  unfold permutationAverage profile
  simp_rw [hv]
  congr 1
  apply Fintype.sum_equiv (Equiv.mulLeft K)
  intro σ
  rfl

/-- A prefix-invariant statistic has a finite binomial-mixture expectation.
This is the exact permutation argument, with no conditioning on null events. -/
theorem expectation_eq_mixture (e : Fin n ≃ V)
    (H : ℝ → (V → ℝ) → ℝ) (hH : PrefixInvariant H)
    (s : ℝ) (hs : 0 ≤ s)
    (hInt : Integrable (H s) (Measure.pi (fun _ : V => expMeasure 1))) :
    (∫ r, H s r ∂Measure.pi (fun _ : V => expMeasure 1)) =
      arrivalMixture n (profile e H) (1 - Real.exp (-s)) := by
  have havg : permutationAverage (H s) =ᵐ[Measure.pi (fun _ : V => expMeasure 1)]
      (fun r => profile e H (rankArrivalCount r s)) := by
    filter_upwards [ae_rawRanks_injective (V := V)] with r hr
    exact permutation_average_eq_profile e H hH r hr s
  rw [integral_eq_of_permutationAverage_ae (expMeasure 1) (H s) _ hInt havg]
  rw [integral_comp_nat_bounded _ (fun r => rankArrivalCount r s)
    (measurable_retainedVertices_card Finset.univ s) n
    (fun r => rankArrivalCount_le_of_equiv e r s)]
  unfold arrivalMixture
  apply Finset.sum_congr rfl
  intro j hj
  have hc : Fintype.card V = n := by simpa using Fintype.card_congr e.symm
  have hm := measureReal_retainedVertices_card (V := V) Finset.univ j s hs
  simpa only [rankArrivalCount,retainedVertices,Finset.card_univ,hc,
    arrivalWeight_formula,sub_sub_cancel] using congrArg (fun x : ℝ => x * profile e H j) hm
end OrderMixture

-- Source: Solutions.PrefixOrderActivity
open RGMISFast
namespace PrefixOrderActivity
variable {V : Type*} [Fintype V] [LinearOrder V]
lemma activity_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s t : ℝ)
    (hlow : ∀ v, r v < s ↔ q v < t)
    (hord : ∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) (v : V) :
    s ≤ tau G r v ↔ t ≤ tau G q v := by
  have hm : ∀ w, r w < s → inMIS G r w = inMIS G q w := by
    intro w
    induction w using (measure (rk r)).wf.induction with
    | h w ih =>
      intro hw
      have hh : inMIS G r w = true ↔ inMIS G q w = true := by
        rw [mis_true_iff,mis_true_iff]
        constructor
        · intro h z ha hz
          have hzs : q z < t := hz.trans ((hlow w).mp hw)
          have hzr := (hlow z).mpr hzs
          have hzw := (hord z w hzr hw).mpr hz
          rw [← ih z (rk_lt r hzw) hzr]
          exact h z ha hzw
        · intro h z ha hz
          have hzs := hz.trans hw
          rw [ih z (rk_lt r hz) hzs]
          exact h z ha ((hord z w hzs hw).mp hz)
      cases hr : inMIS G r w <;> cases hq : inMIS G q w <;> simp_all
  rw [active_vertex_iff,active_vertex_iff]
  constructor
  · intro h w ha hqw
    by_contra hs
    have hwr := (hlow w).mpr (lt_of_not_ge hs)
    have hrw : inMIS G r w = true := (hm w hwr).trans hqw
    exact (not_le_of_gt hwr) (h w ha hrw)
  · intro h w ha hrw
    by_contra hs
    have hwr := lt_of_not_ge hs
    have hqw : inMIS G q w = true := (hm w hwr).symm.trans hrw
    exact (not_le_of_gt ((hlow w).mp hwr)) (h w ha hqw)

lemma Y_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s t : ℝ)
    (h : ∀ v, s ≤ tau G r v ↔ t ≤ tau G q v) (u : V) (k : ℕ) :
    Y G u k s r = Y G u k t q := by
  classical
  unfold Y
  congr 1
  apply Finset.filter_congr
  intro A hA
  have ha : ActiveAt G r s A ↔ ActiveAt G q t A := by
    unfold ActiveAt
    simp_rw [h]
  rw [ha]
lemma dsSum_congr
    (G : SimpleGraph V) [DecidableRel G.Adj] (r q : V → ℝ) (s t : ℝ)
    (h : ∀ v, s ≤ tau G r v ↔ t ≤ tau G q v) (u : V) (k : ℕ) :
    dsSum G u k s r = dsSum G u k t q := by
  classical
  have hc : countedW G u k s r = countedW G u k t q := by
    unfold countedW
    apply Finset.filter_congr
    intro W hw
    have ha : ActiveAt G r s (insert u W) ↔ ActiveAt G q t (insert u W) := by
      unfold ActiveAt
      simp_rw [h]
    rw [ha]
  have he : {v | s ≤ tau G r v} = {v | t ≤ tau G q v} := Set.ext h
  unfold dsSum
  rw [hc,he]
end PrefixOrderActivity

-- Source: Solutions.RootArrivalProfile
open MeasureTheory ProbabilityTheory RGMISFast
set_option maxHeartbeats 1000000
namespace RootArrivalProfile
open Classical ExponentialArrivals OrderMixture ArrivalPolynomial
variable {V : Type*} [Fintype V] [LinearOrder V]
def pin (u : V) (ρ : ℝ) (r : V → ℝ) : V → ℝ := fun v => if v = u then ρ else r v
lemma pin_measurable (u : V) (ρ : ℝ) : Measurable (pin u ρ) := by
  apply measurable_pi_lambda
  intro v
  by_cases h : v = u
  · simpa only [pin,if_pos h] using (measurable_const : Measurable (fun _ : V → ℝ => ρ))
  · simpa only [pin,if_neg h] using (measurable_pi_apply v : Measurable (fun r : V → ℝ => r v))
lemma pin_map (u : V) (ρ : ℝ) :
    (Measure.pi (fun _ : V => expMeasure 1)).map (pin u ρ) = rootLaw u ρ := by
  have hm (v : V) : Measurable (fun x : ℝ => if v = u then ρ else x) := by
    split_ifs <;> fun_prop
  unfold pin
  rw [Measure.pi_map_pi (fun v => (hm v).aemeasurable)]
  unfold rootLaw
  congr 1
  funext v
  by_cases h : v = u <;> simp [h]

lemma pinned_activity_congr (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (r q : V → ℝ) (s t ρ σ : ℝ) (hρ : s ≤ ρ) (hσ : t ≤ σ)
    (hlow : ∀ v, r v < s ↔ q v < t)
    (hord : ∀ v w, r v < s → r w < s → (r v < r w ↔ q v < q w)) (v : V) :
    s ≤ tau G (pin u ρ r) v ↔ t ≤ tau G (pin u σ q) v := by
  apply PrefixOrderActivity.activity_congr
  · intro w
    by_cases h : w = u
    · simp only [pin,if_pos h]
      exact iff_of_false (not_lt_of_ge hρ) (not_lt_of_ge hσ)
    · simpa only [pin,if_neg h] using hlow w
  · intro w z hw hz
    have hwu : w ≠ u := by intro h; simpa [pin,h,not_lt_of_ge hρ] using hw
    have hzu : z ≠ u := by intro h; simpa [pin,h,not_lt_of_ge hρ] using hz
    simp only [pin,if_neg hwu,if_neg hzu] at hw hz ⊢
    exact hord w z hw hz

noncomputable def countProfile (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s : ℝ) (r : V → ℝ) : ℝ := (Y G u k s (pin u s r) : ℝ)
noncomputable def lossProfile (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s : ℝ) (r : V → ℝ) : ℝ := (dsSum G u k s (pin u s r) : ℝ)
lemma count_prefix_invariant (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) :
    PrefixInvariant (countProfile G u k) := by
  intro r q s t hlo hord
  unfold countProfile
  congr 1
  exact PrefixOrderActivity.Y_congr G _ _ s t
    (pinned_activity_congr G u r q s t s t le_rfl le_rfl hlo hord) u k
lemma loss_prefix_invariant (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) :
    PrefixInvariant (lossProfile G u k) := by
  intro r q s t hlo hord
  unfold lossProfile
  congr 1
  exact PrefixOrderActivity.dsSum_congr G _ _ s t
    (pinned_activity_congr G u r q s t s t le_rfl le_rfl hlo hord) u k

lemma count_measurable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) :
    Measurable (countProfile G u k s) :=
  ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (Y_measurable_complete G u k s)).comp (pin_measurable u s)
lemma loss_measurable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) :
    Measurable (lossProfile G u k s) :=
  ((measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (dsSum_measurable_complete G u k s)).comp (pin_measurable u s)
lemma count_integrable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] : Integrable (countProfile G u k s) μ := by
  apply Integrable.of_bound (count_measurable G u k s).aestronglyMeasurable
    (Fintype.card (Finset V) : ℝ)
  filter_upwards [] with r
  rw [countProfile,Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Finset.card_le_univ (α := Finset V) _)
lemma dsSum_bound (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) :
    dsSum G u k s r ≤ Fintype.card (Finset V) * Fintype.card V := by
  calc
    _ ≤ ∑ _W ∈ countedW G u k s r, Fintype.card V :=
      Finset.sum_le_sum (fun W _ => Finset.card_le_univ _)
    _ = (countedW G u k s r).card * Fintype.card V := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (Finset.card_le_univ _)
lemma loss_integrable (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] : Integrable (lossProfile G u k s) μ := by
  apply Integrable.of_bound (loss_measurable G u k s).aestronglyMeasurable
    ((Fintype.card (Finset V) * Fintype.card V : ℕ) : ℝ)
  filter_upwards [] with r
  rw [lossProfile,Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast dsSum_bound G u k s _

lemma count_integral_rootLaw (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s ρ : ℝ) (hρ : s ≤ ρ) :
    (∫ r, (Y G u k s r : ℝ) ∂rootLaw u ρ) =
      ∫ r, countProfile G u k s r ∂Measure.pi (fun _ : V => expMeasure 1) := by
  have hm : Measurable (fun r : V → ℝ => (Y G u k s r : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (Y_measurable_complete G u k s)
  rw [← pin_map,integral_map (pin_measurable u ρ).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with r
  unfold countProfile
  congr 1
  exact PrefixOrderActivity.Y_congr G _ _ s s
    (pinned_activity_congr G u r r s s ρ s hρ le_rfl (fun _ => Iff.rfl)
      (fun _ _ _ _ => Iff.rfl)) u k
lemma loss_integral_rootLaw (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s ρ : ℝ) (hρ : s ≤ ρ) :
    (∫ r, (dsSum G u k s r : ℝ) ∂rootLaw u ρ) =
      ∫ r, lossProfile G u k s r ∂Measure.pi (fun _ : V => expMeasure 1) := by
  have hm : Measurable (fun r : V → ℝ => (dsSum G u k s r : ℝ)) :=
    (measurable_of_countable (fun n : ℕ => (n : ℝ))).comp (dsSum_measurable_complete G u k s)
  rw [← pin_map,integral_map (pin_measurable u ρ).aemeasurable hm.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [] with r
  unfold lossProfile
  congr 1
  exact PrefixOrderActivity.dsSum_congr G _ _ s s
    (pinned_activity_congr G u r r s s ρ s hρ le_rfl (fun _ => Iff.rfl)
      (fun _ _ _ _ => Iff.rfl)) u k
end RootArrivalProfile

-- Source: Solutions.RootCountDriftBound
open MeasureTheory ProbabilityTheory RGMISFast
namespace RootCountDriftBound
open Classical ArrivalAuxiliary RootArrivalProfile
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V]

lemma counted_attached_active (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) (W : Finset V)
    (hW : W ∈ countedW G u k s r) :
    W.card = k ∧ IsAttached (restrictTo G {x | s ≤ tau G r x}) {u} W := by
  obtain ⟨_,hu,hcard,hconn,hact⟩ := Finset.mem_filter.mp hW
  refine ⟨hcard,(singleton_attached_iff _ u W).mpr ⟨hu,?_⟩⟩
  refine ⟨Finset.mem_insert_self _ _,?_⟩
  have he : restrictTo (restrictTo G {x | s ≤ tau G r x}) (↑(insert u W)) =
      restrictTo G (↑(insert u W)) := by
    ext x y
    change ((G.Adj x y ∧ s ≤ tau G r x ∧ s ≤ tau G r y) ∧
      x ∈ insert u W ∧ y ∈ insert u W) ↔
      (G.Adj x y ∧ x ∈ insert u W ∧ y ∈ insert u W)
    constructor
    · rintro ⟨⟨ha,_,_⟩,hx,hy⟩
      exact ⟨ha,hx,hy⟩
    · rintro ⟨ha,hx,hy⟩
      exact ⟨⟨ha,hact x hx,hact y hy⟩,hx,hy⟩
  intro x hx
  rw [he]
  exact hconn.2 x hx

lemma dsSum_lower (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (hk : 1 ≤ k) (s : ℝ) (r : V → ℝ) :
    (k : ℝ) / Real.exp 1 * (Y G u k s r : ℝ) ^ (1+(k:ℝ)⁻¹) ≤
      (dsSum G u k s r : ℝ) := by
  rw [Y_eq_countedW]
  let S := countedW G u k s r
  change (k : ℝ) / Real.exp 1 * (S.card : ℝ) ^ (1+(k:ℝ)⁻¹) ≤ _
  by_cases hS : S.Nonempty
  · have hc : (0 : ℝ) < S.card := by exact_mod_cast hS.card_pos
    have hb := RGMISFast.lemma_5_1 (restrictTo G {x | s ≤ tau G r x}) u k hk S hS
      (fun W hW => counted_attached_active G u k s r W hW)
    have hh := mul_le_mul_of_nonneg_left hb hc.le
    have he : (S.card : ℝ) * ((1 / (S.card : ℝ)) *
        ∑ W ∈ S, (dW (restrictTo G {x | s ≤ tau G r x}) u W : ℝ)) =
        ∑ W ∈ S, (dW (restrictTo G {x | s ≤ tau G r x}) u W : ℝ) := by
      field_simp
    rw [he] at hh
    simp only [one_div] at hh
    rw [Real.rpow_add hc,Real.rpow_one]
    simpa only [dsSum,Nat.cast_sum,S,mul_assoc,mul_left_comm,mul_comm] using hh
  · have he : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    have hp : (1+(k:ℝ)⁻¹) ≠ 0 := by positivity
    simp only [he,Finset.card_empty,Nat.cast_zero,Real.zero_rpow hp,mul_zero]
    positivity

lemma Y_real_measurable (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s : ℝ) : Measurable (fun r : V → ℝ => (Y G u k s r : ℝ)) :=
  (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (Y_measurable_complete G u k s)
lemma D_real_measurable (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s : ℝ) : Measurable (fun r : V → ℝ => (dsSum G u k s r : ℝ)) :=
  (measurable_of_countable (fun m : ℕ => (m : ℝ))).comp (dsSum_measurable_complete G u k s)
lemma Y_integrable (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s : ℝ) (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun r => (Y G u k s r : ℝ)) μ := by
  apply Integrable.of_bound (Y_real_measurable G u k s).aestronglyMeasurable
    (Fintype.card (Finset V) : ℝ)
  filter_upwards [] with r
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast (Finset.card_le_univ (α := Finset V) _)
lemma D_integrable (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s : ℝ) (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun r => (dsSum G u k s r : ℝ)) μ := by
  apply Integrable.of_bound (D_real_measurable G u k s).aestronglyMeasurable
    ((Fintype.card (Finset V) * Fintype.card V : ℕ) : ℝ)
  filter_upwards [] with r
  rw [Real.norm_of_nonneg (Nat.cast_nonneg _)]
  exact_mod_cast dsSum_bound G u k s r
lemma power_integrable (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s p : ℝ) (hp : 0 ≤ p)
    (μ : Measure (V → ℝ)) [IsFiniteMeasure μ] :
    Integrable (fun r => (Y G u k s r : ℝ) ^ p) μ := by
  apply Integrable.of_bound
    ((Real.continuous_rpow_const hp).measurable.comp (Y_real_measurable G u k s)).aestronglyMeasurable
    ((Fintype.card (Finset V) : ℝ) ^ p)
  filter_upwards [] with r
  simp only [Function.comp_apply]
  rw [Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)]
  apply Real.rpow_le_rpow (Nat.cast_nonneg _) _ hp
  exact_mod_cast (Finset.card_le_univ (α := Finset V) _)

lemma expectation_drift_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (hk : 1 ≤ k) (s : ℝ)
    (μ : Measure (V → ℝ)) [IsProbabilityMeasure μ] :
    (k : ℝ) / Real.exp 1 * (∫ r, (Y G u k s r : ℝ) ∂μ) ^ (1+(k:ℝ)⁻¹) ≤
      ∫ r, (dsSum G u k s r : ℝ) ∂μ := by
  have hp : (0 : ℝ) ≤ 1+(k:ℝ)⁻¹ := by positivity
  have hj := (convexOn_rpow (show (1 : ℝ) ≤ 1+(k:ℝ)⁻¹ from le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _)))).map_integral_le
    (Real.continuous_rpow_const hp).continuousOn isClosed_Ici
    (Filter.Eventually.of_forall (fun r => (show (0 : ℝ) ≤ (Y G u k s r : ℝ) by positivity)))
    (Y_integrable G u k s μ) (power_integrable G u k s _ hp μ)
  have hi := integral_mono ((power_integrable G u k s _ hp μ).const_mul ((k:ℝ)/Real.exp 1))
    (D_integrable G u k s μ) (fun r => dsSum_lower G u k hk s r)
  rw [integral_const_mul] at hi
  exact (mul_le_mul_of_nonneg_left hj (by positivity)).trans hi
end RootCountDriftBound

-- Source: Solutions.PrescribedDecay
set_option autoImplicit false
namespace PrescribedDecay

open Set

/-- The negative inverse power converts the nonlinear differential inequality
into a lower bound on its derivative. -/
theorem inverse_power_derivative_lower (y v c : ℝ) (k : ℕ)
    (hy : 0 < y) (hk : 0 < k)
    (hv : v ≤ -(k : ℝ) * c * y ^ (1 + (k : ℝ)⁻¹)) :
    c ≤ v * (-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hcoeff : (-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (inv_nonneg.mpr hkpos.le))
      (Real.rpow_nonneg hy.le _)
  have hmul := mul_le_mul_of_nonpos_right hv hcoeff
  have hidentity : (-(k : ℝ) * c * y ^ (1 + (k : ℝ)⁻¹)) *
      ((-(k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1)) = c := by
    calc
      _ = (k : ℝ) * (k : ℝ)⁻¹ * c *
          (y ^ (1 + (k : ℝ)⁻¹) * y ^ (-(k : ℝ)⁻¹ - 1)) := by ring
      _ = c := by
        rw [← Real.rpow_add hy]
        have hexp : (1 + (k : ℝ)⁻¹) + (-(k : ℝ)⁻¹ - 1) = 0 := by ring
        rw [hexp, Real.rpow_zero, mul_inv_cancel₀ hkpos.ne']
        ring
  rw [hidentity] at hmul
  nlinarith [hmul]

/-- Integration with an arbitrary differentiable clock. This stronger form
retains the initial value and requires strict positivity of the function. -/
theorem inverse_power_clock_growth
    (f f' q q' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hfcont : ContinuousOn f (Icc 0 a)) (hqcont : ContinuousOn q (Icc 0 a))
    (hfpos : ∀ t ∈ Icc 0 a, 0 < f t)
    (hfderiv : ∀ t ∈ Ioo 0 a, HasDerivAt f (f' t) t)
    (hqderiv : ∀ t ∈ Ioo 0 a, HasDerivAt q (q' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      f' t ≤ -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹)) :
    f 0 ^ (-(k : ℝ)⁻¹) + (q a - q 0) ≤ f a ^ (-(k : ℝ)⁻¹) := by
  let F : ℝ → ℝ := fun t ↦ f t ^ (-(k : ℝ)⁻¹) - q t
  have hFcont : ContinuousOn F (Icc 0 a) :=
    (hfcont.rpow_const (fun t ht ↦ Or.inl (hfpos t ht).ne')).sub hqcont
  have hFderiv (t : ℝ) (ht : t ∈ Ioo 0 a) :
      HasDerivAt F
        (f' t * (-(k : ℝ)⁻¹) * f t ^ (-(k : ℝ)⁻¹ - 1) - q' t) t :=
    ((hfderiv t ht).rpow_const (Or.inl (hfpos t ⟨ht.1.le, ht.2.le⟩).ne')).sub
      (hqderiv t ht)
  have hmono : MonotoneOn F (Icc 0 a) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 a) hFcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hFderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hFderiv t ht).deriv]
      have h := inverse_power_derivative_lower (f t) (f' t) (q' t) k
        (hfpos t ⟨ht.1.le, ht.2.le⟩) hk (hode t ht)
      linarith
  have hends := hmono (show (0 : ℝ) ∈ Icc 0 a from ⟨le_rfl, ha.le⟩)
    (show a ∈ Icc 0 a from ⟨ha.le, le_rfl⟩) ha.le
  dsimp [F] at hends
  linarith

/-- Turning a lower bound on a negative inverse power back into an ordinary
power upper bound. -/
theorem le_inverse_pow_of_inverse_power_lower (y L : ℝ) (k : ℕ)
    (hy : 0 < y) (hL : 0 < L) (hk : 0 < k)
    (h : L ≤ y ^ (-(k : ℝ)⁻¹)) :
    y ≤ (L⁻¹) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hh := Real.rpow_le_rpow_of_nonpos hL h (neg_nonpos.mpr hkpos.le)
  rw [← Real.rpow_mul hy.le] at hh
  have hexp : (-(k : ℝ)⁻¹) * (-(k : ℝ)) = 1 := by field_simp
  rw [hexp, Real.rpow_one, Real.rpow_neg hL.le, Real.rpow_natCast, ← inv_pow] at hh
  exact hh

/-- The nonnegative version needs no strict positivity assumption: the ODE
makes `f` nonincreasing, so either the endpoint is zero or the whole interval
has positive values and the inverse-power argument applies. -/
theorem power_decay_bound_with_clock
    (f f' q q' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hfcont : ContinuousOn f (Icc 0 a)) (hqcont : ContinuousOn q (Icc 0 a))
    (hfnonneg : ∀ t ∈ Icc 0 a, 0 ≤ f t)
    (hqnonneg : ∀ t ∈ Ioo 0 a, 0 ≤ q' t)
    (hfderiv : ∀ t ∈ Ioo 0 a, HasDerivAt f (f' t) t)
    (hqderiv : ∀ t ∈ Ioo 0 a, HasDerivAt q (q' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      f' t ≤ -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹))
    (hclock : 0 < q a - q 0) :
    f a ≤ ((q a - q 0)⁻¹) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast hk
  have hazero : (0 : ℝ) ∈ Icc 0 a := ⟨le_rfl, ha.le⟩
  have haend : a ∈ Icc 0 a := ⟨ha.le, le_rfl⟩
  have hanti : AntitoneOn f (Icc 0 a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Icc 0 a) hfcont
    · intro t ht
      rw [interior_Icc] at ht
      exact (hfderiv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(hfderiv t ht).deriv]
      have hnonpos : -(k : ℝ) * q' t * f t ^ (1 + (k : ℝ)⁻¹) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg
          (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hkpos.le) (hqnonneg t ht))
          (Real.rpow_nonneg (hfnonneg t ⟨ht.1.le, ht.2.le⟩) _)
      exact (hode t ht).trans hnonpos
  by_cases hzero : f a = 0
  · rw [hzero]
    exact pow_nonneg (inv_nonneg.mpr hclock.le) _
  · have hfapos : 0 < f a := lt_of_le_of_ne (hfnonneg a haend) (Ne.symm hzero)
    have hfpos : ∀ t ∈ Icc 0 a, 0 < f t := by
      intro t ht
      exact hfapos.trans_le (hanti ht haend ht.2)
    have hgrowth := inverse_power_clock_growth f f' q q' a k ha hk
      hfcont hqcont hfpos hfderiv hqderiv hode
    have hlow : q a - q 0 ≤ f a ^ (-(k : ℝ)⁻¹) := by
      have hinit := Real.rpow_nonneg (hfnonneg 0 hazero) (-(k : ℝ)⁻¹)
      linarith
    exact le_inverse_pow_of_inverse_power_lower (f a) (q a - q 0) k
      hfapos hclock hk hlow

/-- The autonomous version after the time change `s = -log (1-t)`. -/
theorem power_decay_bound
    (g g' : ℝ → ℝ) (a : ℝ) (k : ℕ) (ha : 0 < a) (hk : 0 < k)
    (hgcont : ContinuousOn g (Icc 0 a))
    (hgnonneg : ∀ t ∈ Icc 0 a, 0 ≤ g t)
    (hgderiv : ∀ t ∈ Ioo 0 a, HasDerivAt g (g' t) t)
    (hode : ∀ t ∈ Ioo 0 a,
      g' t ≤ -(k : ℝ) / Real.exp 1 * g t ^ (1 + (k : ℝ)⁻¹)) :
    g a ≤ (Real.exp 1 / a) ^ k := by
  have h := power_decay_bound_with_clock g g' (fun t ↦ t / Real.exp 1)
    (fun _ ↦ 1 / Real.exp 1) a k ha hk hgcont
    (continuous_id.div_const _).continuousOn hgnonneg
    (fun _ _ ↦ by positivity) hgderiv
    (fun t _ ↦ (hasDerivAt_id t).div_const (Real.exp 1))
    (fun t ht ↦ by simpa only [div_eq_mul_inv, one_mul] using hode t ht)
    (by simp only [zero_div, sub_zero]; positivity)
  simpa only [zero_div, sub_zero, inv_div] using h


end PrescribedDecay

-- Source: Solutions.PermutationRankSwap
open Classical
namespace PermutationRankSwap
open OrderMixture
variable {V : Type*} [Fintype V] [DecidableEq V] {n : ℕ}
def swapRanks (e : Fin n ≃ V) (j l : Fin n) : Equiv.Perm V := Equiv.swap (e j) (e l)
lemma rank_swap_eq_below (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n)
    (hl : j ≤ l) (v : V) (hv : representative e σ v < (j.val : ℝ)) :
    representative e (swapRanks e j l * σ) v = representative e σ v := by
  have hpos : (e.symm (σ v)).val < j.val := by
    unfold representative at hv
    exact_mod_cast hv
  have ha : σ v ≠ e j := by intro h; simp only [h,Equiv.symm_apply_apply] at hpos; omega
  have hb : σ v ≠ e l := by intro h; simp only [h,Equiv.symm_apply_apply] at hpos; exact (not_lt_of_ge hl) hpos
  simp only [representative,Equiv.Perm.mul_apply,swapRanks,Equiv.swap_apply_of_ne_of_ne ha hb]
lemma rank_swap_low_iff (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n)
    (hl : j ≤ l) (v : V) :
    representative e σ v < (j.val : ℝ) ↔
      representative e (swapRanks e j l * σ) v < (j.val : ℝ) := by
  constructor
  · intro h
    rw [rank_swap_eq_below e σ j l hl v h]
    exact h
  · intro h
    have hh := rank_swap_eq_below e (swapRanks e j l * σ) j l hl v h
    have he : swapRanks e j l * (swapRanks e j l * σ) = σ := by
      ext w
      simp [swapRanks,Equiv.Perm.mul_apply]
    rw [he] at hh
    rwa [← hh] at h
lemma swap_next_rank (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n) :
    representative e (swapRanks e j l * σ) (σ.symm (e l)) = (j.val : ℝ) := by
  simp [representative,swapRanks,Equiv.Perm.mul_apply]
lemma rank_injective (e : Fin n ≃ V) (σ : Equiv.Perm V) :
    Function.Injective (representative e σ) := by
  intro v w h
  apply σ.injective
  apply e.symm.injective
  apply Fin.ext
  unfold representative at h
  exact_mod_cast h
lemma rank_interval_unique (e : Fin n ≃ V) (σ : Equiv.Perm V) (j l : Fin n) (v : V)
    (hv : (j.val : ℝ) ≤ representative e (swapRanks e j l * σ) v ∧
      representative e (swapRanks e j l * σ) v < (j.val : ℝ) + 1) : v = σ.symm (e l) := by
  apply rank_injective e (swapRanks e j l * σ)
  rw [swap_next_rank]
  unfold representative at hv ⊢
  have ha : j.val ≤ (e.symm ((swapRanks e j l * σ) v)).val := by exact_mod_cast hv.1
  have hb : (e.symm ((swapRanks e j l * σ) v)).val < j.val + 1 := by exact_mod_cast hv.2
  exact_mod_cast (show (e.symm ((swapRanks e j l * σ) v)).val = j.val by omega)
end PermutationRankSwap

-- Source: Solutions.ArrivalLoss
open RGMISFast
open scoped BigOperators
namespace ArrivalLoss
open Classical
section
variable {V : Type*} [Fintype V] [DecidableEq V]
omit [Fintype V] in
/-- The number lost under one arrival is the number of sets it kills. -/
theorem count_loss_eq_killed {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (kill : ι → Finset V) (w : V) :
    (F.card : ℝ) - ((F.filter fun i => w ∉ kill i).card : ℝ) =
      ((F.filter fun i => w ∈ kill i).card : ℝ) := by
  have h := Finset.card_filter_add_card_filter_not
    (s := F) (p := fun i => w ∈ kill i)
  have hr : ((F.filter fun i => w ∈ kill i).card : ℝ) +
      ((F.filter fun i => w ∉ kill i).card : ℝ) = (F.card : ℝ) := by
    exact_mod_cast h
  linarith

omit [Fintype V] in
/-- Exact double counting of the total loss over all possible arrivals. -/
theorem sum_count_loss_eq_sum_killing_card {ι : Type*} [DecidableEq ι]
    (F : Finset ι) (R : Finset V) (kill : ι → Finset V)
    (hkill : ∀ i ∈ F, kill i ⊆ R) :
    ∑ w ∈ R, ((F.card : ℝ) - ((F.filter fun i => w ∉ kill i).card : ℝ)) =
      ∑ i ∈ F, ((kill i).card : ℝ) := by
  simp_rw [count_loss_eq_killed]
  have hind (w : V) : ((F.filter fun i => w ∈ kill i).card : ℝ) =
      ∑ i ∈ F, if w ∈ kill i then (1 : ℝ) else 0 := by simp
  simp_rw [hind]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Finset.inter_eq_right.mpr (hkill i hi)]

noncomputable def killers (H : SimpleGraph V) (u : V) (W : Finset V) : Finset V :=
  Finset.univ.filter (fun x => x ≠ u ∧ (x ∈ W ∨ ∃ y ∈ insert u W, H.Adj y x))

lemma killers_card (H : SimpleGraph V) (u : V) (W : Finset V) :
    (killers H u W).card = dW H u W := rfl

end

/-- Exact finite loss identity for the mission's active graph and counted family. -/
theorem dsSum_eq_total_loss {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) :
    (dsSum G u k s r : ℝ) =
      ∑ x ∈ (Finset.univ.filter (fun x => x ≠ u ∧ s ≤ tau G r x)),
        ((countedW G u k s r).card -
          (((countedW G u k s r).filter
            (fun W => x ∉ killers (restrictTo G {v | s ≤ tau G r v}) u W)).card : ℝ)) := by
  let F := countedW G u k s r
  let R := Finset.univ.filter (fun x => x ≠ u ∧ s ≤ tau G r x)
  let kill := killers (restrictTo G {v | s ≤ tau G r v}) u
  have hkill : ∀ W ∈ F, kill W ⊆ R := by
    intro W hW x hx
    obtain ⟨hne, hxW | ⟨y,hy,hyx⟩⟩ := (Finset.mem_filter.mp hx).2
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, hne, ?_⟩
      have hact := (Finset.mem_filter.mp hW).2.2.2.2
      exact hact x (Finset.mem_insert_of_mem hxW)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hne,hyx.2.2⟩
  have h := sum_count_loss_eq_sum_killing_card F R kill hkill
  rw [h]
  simp only [dsSum, Nat.cast_sum, killers_card, F, kill]
end ArrivalLoss

-- Source: Solutions.ArrivalCountTransition
open RGMISFast
open Classical
namespace ArrivalLoss
variable {V : Type*} [Fintype V] [LinearOrder V]

lemma active_insert_transition
    (G : SimpleGraph V) [DecidableRel G.Adj] (u x : V) (W : Finset V)
    (r : V → ℝ) (s t : ℝ) (hst : s ≤ t) (hxu : x ≠ u)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    ActiveAt G r t (insert u W) ↔ ActiveAt G r s (insert u W) ∧
      x ∉ killers (restrictTo G {v | s ≤ tau G r v}) u W := by
  rw [SingleArrival.active_set_transition G r s t hst x (insert u W) hx hone]
  constructor
  · rintro ⟨ha,hkeep⟩
    refine ⟨ha,?_⟩
    intro hk
    obtain ⟨_,hw | ⟨y,hy,hyx⟩⟩ := (Finset.mem_filter.mp hk).2
    · exact (hkeep (ha x (Finset.mem_insert_of_mem hw)) x
        (Finset.mem_insert_of_mem hw)).1 rfl
    · exact (hkeep hyx.2.2 y hy).2 hyx.1
  · rintro ⟨ha,hkeep⟩
    refine ⟨ha,?_⟩
    intro hxa v hv
    constructor
    · intro hvx
      subst v
      have hxW : x ∈ W := (Finset.mem_insert.mp hv).resolve_left hxu
      exact hkeep (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxu,Or.inl hxW⟩)
    · intro hadj
      exact hkeep (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hxu,
        Or.inr ⟨v,hv,hadj,ha v hv,hxa⟩⟩)

/-- The actual counted family after a single nonroot arrival is exactly the
old family with the sets killed by that arrival removed. -/
theorem countedW_single_arrival
    (G : SimpleGraph V) [DecidableRel G.Adj] (u x : V) (k : ℕ)
    (r : V → ℝ) (s t : ℝ) (hst : s ≤ t) (hxu : x ≠ u)
    (hx : s ≤ r x ∧ r x < t)
    (hone : ∀ w, s ≤ r w → r w < t → w = x) :
    countedW G u k t r = (countedW G u k s r).filter
      (fun W => x ∉ killers (restrictTo G {v | s ≤ tau G r v}) u W) := by
  ext W
  simp only [countedW,Finset.mem_filter,Finset.mem_univ,true_and]
  rw [active_insert_transition G u x W r s t hst hxu hx hone]
  tauto

end ArrivalLoss

-- Source: Solutions.PermutationGraphTransition
open RGMISFast
namespace PermutationGraphTransition
open Classical RootArrivalProfile OrderMixture PermutationRankSwap ArrivalLoss ArrivalAuxiliary
variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
noncomputable def ranks (e : Fin n ≃ V) (u : V) (σ : Equiv.Perm V) : V → ℝ :=
  pin u (n : ℝ) (representative e σ)
lemma activity_before_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (σ : Equiv.Perm V) (j l : Fin n) (hl : j ≤ l) (v : V) :
    (j.val : ℝ) ≤ tau G (ranks e u σ) v ↔
      (j.val : ℝ) ≤ tau G (ranks e u (swapRanks e j l * σ)) v := by
  apply pinned_activity_congr
  · exact_mod_cast j.isLt.le
  · exact_mod_cast j.isLt.le
  · exact rank_swap_low_iff e σ j l hl
  · intro w z hw hz
    rw [rank_swap_eq_below e σ j l hl w hw,rank_swap_eq_below e σ j l hl z hz]
lemma family_before_swap (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (σ : Equiv.Perm V) (j l : Fin n) (hl : j ≤ l) :
    countedW G u k (j.val : ℝ) (ranks e u σ) =
      countedW G u k (j.val : ℝ) (ranks e u (swapRanks e j l * σ)) := by
  unfold countedW
  apply Finset.filter_congr
  intro W hw
  have ha : ActiveAt G (ranks e u σ) (j.val : ℝ) (insert u W) ↔
      ActiveAt G (ranks e u (swapRanks e j l * σ)) (j.val : ℝ) (insert u W) := by
    unfold ActiveAt
    simp_rw [activity_before_swap G e u σ j l hl]
  rw [ha]

lemma next_family (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (σ : Equiv.Perm V) (j l : Fin n) (hl : j ≤ l) :
    countedW G u k ((j.val : ℝ)+1) (ranks e u (swapRanks e j l * σ)) =
      (countedW G u k (j.val : ℝ) (ranks e u σ)).filter
        (fun W => σ.symm (e l) ∉ killers
          (restrictTo G {v | (j.val : ℝ) ≤ tau G (ranks e u σ) v}) u W) := by
  let r := ranks e u (swapRanks e j l * σ)
  let x := σ.symm (e l)
  have hn : (j.val : ℝ) + 1 ≤ n := by exact_mod_cast j.isLt
  have hroot : r u = n := by simp [r,ranks,pin]
  have hone : ∀ w, (j.val : ℝ) ≤ r w → r w < (j.val : ℝ)+1 → w = x := by
    intro w hw ht
    have hwu : w ≠ u := by intro he; subst w; rw [hroot] at ht; linarith
    apply rank_interval_unique e σ j l w
    simpa only [r,ranks,pin,if_neg hwu] using And.intro hw ht
  have hc := family_before_swap G e u k σ j l hl
  have hg : {v | (j.val : ℝ) ≤ tau G (ranks e u σ) v} =
      {v | (j.val : ℝ) ≤ tau G r v} :=
    Set.ext (activity_before_swap G e u σ j l hl)
  by_cases hxu : x = u
  · have hnone : ∀ w, ¬ ((j.val : ℝ) ≤ r w ∧ r w < (j.val : ℝ)+1) := by
      intro w hw
      have he := (hone w hw.1 hw.2).trans hxu
      rw [he,hroot] at hw
      linarith [hw.2]
    have hsame : countedW G u k ((j.val : ℝ)+1) r = countedW G u k (j.val : ℝ) r := by
      unfold countedW
      apply Finset.filter_congr
      intro W hw
      have ha : ActiveAt G r ((j.val : ℝ)+1) (insert u W) ↔
          ActiveAt G r (j.val : ℝ) (insert u W) := by
        unfold ActiveAt
        simp_rw [← activity_no_arrival G r (j.val : ℝ) ((j.val : ℝ)+1) (by linarith) hnone]
      rw [ha]
    change countedW G u k ((j.val : ℝ)+1) r = _
    rw [hsame,← hc]
    have he : σ.symm (e l) = u := hxu
    simp [he,killers]
  · have hx : (j.val : ℝ) ≤ r x ∧ r x < (j.val : ℝ)+1 := by
      have hrx : r x = (j.val : ℝ) := by
        simp only [r,ranks,pin,if_neg hxu]
        exact swap_next_rank e σ j l
      rw [hrx]
      constructor <;> linarith
    change countedW G u k ((j.val : ℝ)+1) r = _
    rw [countedW_single_arrival G u x k r (j.val : ℝ) ((j.val : ℝ)+1)
      (by linarith) hxu hx hone,← hc,← hg]
end PermutationGraphTransition

-- Source: Solutions.PermutationTotalLoss
open RGMISFast
namespace PermutationTotalLoss
open Classical RootArrivalProfile OrderMixture PermutationRankSwap PermutationGraphTransition
open ArrivalLoss ArrivalAuxiliary
variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
lemma killing_position (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k j : ℕ) (σ : Equiv.Perm V)
    (W : Finset V) (hW : W ∈ countedW G u k (j : ℝ) (ranks e u σ))
    (x : V) (hx : x ∈ killers (restrictTo G {v | (j : ℝ) ≤ tau G (ranks e u σ) v}) u W) :
    j ≤ (e.symm (σ x)).val := by
  obtain ⟨hne,hxW | ⟨y,hy,hyx⟩⟩ := (Finset.mem_filter.mp hx).2
  · have hact := (Finset.mem_filter.mp hW).2.2.2.2
    have hh := active_le_rank G (ranks e u σ) j x (hact x (Finset.mem_insert_of_mem hxW))
    simp only [ranks,pin,if_neg hne,representative] at hh
    exact_mod_cast hh
  · have hh := active_le_rank G (ranks e u σ) j x hyx.2.2
    simp only [ranks,pin,if_neg hne,representative] at hh
    exact_mod_cast hh

lemma total_loss (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (σ : Equiv.Perm V) (j : Fin n) :
    (∑ l ∈ Finset.Ici j,
      ((Y G u k (j.val : ℝ) (ranks e u σ) : ℝ) -
        (Y G u k ((j.val : ℝ)+1) (ranks e u (swapRanks e j l * σ)) : ℝ))) =
      (dsSum G u k (j.val : ℝ) (ranks e u σ) : ℝ) := by
  let F := countedW G u k (j.val : ℝ) (ranks e u σ)
  let kill := killers (restrictTo G {v | (j.val : ℝ) ≤ tau G (ranks e u σ) v}) u
  let R := Finset.univ.filter (fun x => j.val ≤ (e.symm (σ x)).val)
  have hkill : ∀ W ∈ F, kill W ⊆ R := by
    intro W hW x hx
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,killing_position G e u k j.val σ W hW x hx⟩
  let loss := fun x => (F.card : ℝ) - ((F.filter fun W => x ∉ kill W).card : ℝ)
  have hsum : (∑ l ∈ Finset.Ici j, loss (σ.symm (e l))) = ∑ x ∈ R, loss x := by
    apply Finset.sum_bij (fun l _ => σ.symm (e l))
    · intro l hl
      simpa [R] using (Finset.mem_Ici.mp hl)
    · intro l hl m hm he
      exact e.injective (σ.symm.injective he)
    · intro x hx
      refine ⟨e.symm (σ x), ?_, ?_⟩
      · simpa [R] using hx
      · simp
    · intro l hl
      rfl
  have htotal := sum_count_loss_eq_sum_killing_card F R kill hkill
  calc
    _ = ∑ l ∈ Finset.Ici j, loss (σ.symm (e l)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [Y_eq_countedW,Y_eq_countedW,next_family G e u k σ j l (Finset.mem_Ici.mp hl)]
    _ = ∑ W ∈ F, ((kill W).card : ℝ) := hsum.trans htotal
    _ = _ := by simp only [dsSum,Nat.cast_sum,F,kill,killers_card]

lemma terminal_loss_zero (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (σ : Equiv.Perm V) :
    dsSum G u k (n : ℝ) (ranks e u σ) = 0 := by
  unfold dsSum
  apply Finset.sum_eq_zero
  intro W hW
  rw [← killers_card]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hh := killing_position G e u k n σ W hW x hx
  exact (not_le_of_gt (e.symm (σ x)).isLt) hh
end PermutationTotalLoss

-- Source: Solutions.FiniteProfileDrift
open RGMISFast
set_option maxHeartbeats 1000000
namespace FiniteProfileDrift
open Classical RootArrivalProfile OrderMixture PermutationRankSwap PermutationGraphTransition
open PermutationTotalLoss ArrivalPolynomial
variable {V : Type*} [Fintype V] [LinearOrder V] {n : ℕ}
lemma countProfile_eq_ranks (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k j : ℕ) (hj : j ≤ n) (σ : Equiv.Perm V) :
    countProfile G u k (j : ℝ) (representative e σ) = (Y G u k (j : ℝ) (ranks e u σ) : ℝ) := by
  unfold countProfile
  congr 1
  apply PrefixOrderActivity.Y_congr
  exact pinned_activity_congr G u _ _ j j j n le_rfl (by exact_mod_cast hj)
    (fun _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
lemma lossProfile_eq_ranks (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k j : ℕ) (hj : j ≤ n) (σ : Equiv.Perm V) :
    lossProfile G u k (j : ℝ) (representative e σ) = (dsSum G u k (j : ℝ) (ranks e u σ) : ℝ) := by
  unfold lossProfile
  congr 1
  apply PrefixOrderActivity.dsSum_congr
  exact pinned_activity_congr G u _ _ j j j n le_rfl (by exact_mod_cast hj)
    (fun _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)

lemma profile_loss_identity (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k j : ℕ) (hj : j < n) :
    profile e (lossProfile G u k) j = (n-j : ℕ) *
      (profile e (countProfile G u k) j - profile e (countProfile G u k) (j+1)) := by
  let ij : Fin n := ⟨j,hj⟩
  have hs (l : Fin n) :
      (∑ σ : Equiv.Perm V, (Y G u k ((j : ℝ)+1) (ranks e u (swapRanks e ij l * σ)) : ℝ)) =
        ∑ σ : Equiv.Perm V, (Y G u k ((j : ℝ)+1) (ranks e u σ) : ℝ) := by
    apply Fintype.sum_equiv (Equiv.mulLeft (swapRanks e ij l))
    intro σ
    rfl
  unfold profile
  simp_rw [lossProfile_eq_ranks G e u k j hj.le,
    countProfile_eq_ranks G e u k j hj.le,
    countProfile_eq_ranks G e u k (j+1) (Nat.succ_le_of_lt hj)]
  simp only [Nat.cast_add,Nat.cast_one]
  have ht (σ : Equiv.Perm V) := total_loss G e u k σ ij
  simp only [ij] at ht
  simp_rw [← ht]
  rw [Finset.sum_comm]
  simp only [Finset.sum_sub_distrib]
  simp only [ij] at hs
  simp only [hs]
  simp only [Finset.sum_const,Fin.card_Ici,nsmul_eq_mul,ij]
  ring

lemma profile_loss_terminal (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) : profile e (lossProfile G u k) n = 0 := by
  unfold profile
  simp_rw [lossProfile_eq_ranks G e u k n le_rfl,terminal_loss_zero]
  simp

lemma loss_mixture_eq_drift (G : SimpleGraph V) [DecidableRel G.Adj]
    (e : Fin n ≃ V) (u : V) (k : ℕ) (z : ℝ) :
    arrivalMixture n (profile e (lossProfile G u k)) z =
      arrivalDrift n (profile e (countProfile G u k)) z := by
  unfold arrivalMixture arrivalDrift
  rw [Finset.sum_range_succ,profile_loss_terminal]
  simp only [mul_zero,add_zero]
  apply Finset.sum_congr rfl
  intro j hj
  rw [profile_loss_identity G e u k j (Finset.mem_range.mp hj)]
  ring
end FiniteProfileDrift

-- Source: Solutions.ArrivalExpansionDerivative
set_option autoImplicit false

lemma arrival_expansion_derivative (n : ℕ) (coeff : ℕ → ℝ) (s : ℝ) :
    HasDerivAt (fun z : ℝ => ∑ j ∈ Finset.range (n+1), coeff j * Real.exp (-(j:ℝ)*z))
      (-(∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s))) s := by
  have hd (j : ℕ) : HasDerivAt
      (fun z : ℝ => coeff j * Real.exp (-(j:ℝ)*z))
      (coeff j * (Real.exp (-(j:ℝ)*s) * (-(j:ℝ)))) s := by
    simpa using (((hasDerivAt_id s).const_mul (-(j:ℝ))).exp.const_mul (coeff j))
  have hh := HasDerivAt.fun_sum (u := Finset.range (n+1)) (fun j _ => hd j)
  have he : (∑ j ∈ Finset.range (n+1), coeff j * (Real.exp (-(j:ℝ)*s) * (-(j:ℝ)))) =
      -(∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [he] at hh
  exact hh

lemma derivative_from_arrival_expansion (f d : ℝ → ℝ) (n : ℕ) (coeff : ℕ → ℝ)
    (t : ℝ)
    (hf : ∀ s ∈ Set.Icc 0 t, f s = ∑ j ∈ Finset.range (n+1), coeff j*Real.exp (-(j:ℝ)*s))
    (hd : ∀ s ∈ Set.Icc 0 t, d s = ∑ j ∈ Finset.range (n+1), (j:ℝ)*coeff j*Real.exp (-(j:ℝ)*s))
    (s : ℝ) (hs : s ∈ Set.Ico 0 t) : HasDerivWithinAt f (-d s) (Set.Icc 0 t) s := by
  have hs' : s ∈ Set.Icc 0 t := ⟨hs.1,hs.2.le⟩
  rw [hd s hs']
  exact (arrival_expansion_derivative n coeff s).hasDerivWithinAt.congr_of_mem hf hs'

-- Source: Solutions.ExponentialPolynomial
open scoped BigOperators
namespace ArrivalPolynomial

lemma exponential_mixture_derivative (n : ℕ) (g : ℕ → ℝ) (s : ℝ) :
    HasDerivAt (fun z => arrivalMixture n g (1 - Real.exp (-z)))
      (-arrivalDrift n g (1 - Real.exp (-s))) s := by
  by_cases hn : n = 0
  · subst n
    simpa [arrivalMixture,arrivalWeight,bernsteinPolynomial,arrivalDrift] using
      (hasDerivAt_const s (g 0))
  · have hq : HasDerivAt (fun z : ℝ => 1 - Real.exp (-z)) (Real.exp (-s)) s := by
      simpa using ((hasDerivAt_id s).neg.exp.const_sub 1)
    have he := Real.exp_pos (-s)
    have hd := (hasDerivAt_arrivalMixture n g (1 - Real.exp (-s))
      (Nat.pos_of_ne_zero hn) (by linarith)).comp s hq
    convert! hd using 1 <;> field_simp <;> ring

/-- The permutation means are Bernstein coefficients. After substituting
1-exp(-s), conversion to monomials supplies the constant exponential coefficients
and simultaneously the weighted coefficients of the exact loss profile. -/
theorem exponential_mixture_expansion (n : ℕ) (g : ℕ → ℝ) :
    ∃ m : ℕ, ∃ coeff : ℕ → ℝ,
      (∀ s : ℝ, arrivalMixture n g (1 - Real.exp (-s)) =
        ∑ j ∈ Finset.range (m+1), coeff j * Real.exp (-(j:ℝ)*s)) ∧
      (∀ s : ℝ, arrivalDrift n g (1 - Real.exp (-s)) =
        ∑ j ∈ Finset.range (m+1), (j:ℝ)*coeff j * Real.exp (-(j:ℝ)*s)) := by
  let P : Polynomial ℝ := ∑ j ∈ Finset.range (n+1),
    (bernsteinPolynomial ℝ n j).comp (1 - Polynomial.X) * Polynomial.C (g j)
  have hp (s : ℝ) : P.eval (Real.exp (-s)) = arrivalMixture n g (1 - Real.exp (-s)) := by
    simp [P,arrivalMixture,arrivalWeight,Polynomial.eval_finsetSum]
  have hf (s : ℝ) : arrivalMixture n g (1 - Real.exp (-s)) =
      ∑ j ∈ Finset.range (P.natDegree+1), P.coeff j * Real.exp (-(j:ℝ)*s) := by
    rw [← hp,Polynomial.eval_eq_sum_range]
    apply Finset.sum_congr rfl
    intro j hj
    congr 1
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  refine ⟨P.natDegree,P.coeff,hf,?_⟩
  intro s
  have hd := exponential_mixture_derivative n g s
  have he : (fun z => arrivalMixture n g (1 - Real.exp (-z))) =
      (fun z => ∑ j ∈ Finset.range (P.natDegree+1), P.coeff j * Real.exp (-(j:ℝ)*z)) := funext hf
  rw [he] at hd
  have hh := hd.unique (arrival_expansion_derivative P.natDegree P.coeff s)
  exact neg_injective hh
end ArrivalPolynomial

-- Source: Solutions.RootArrivalExpansionComplete
open MeasureTheory ProbabilityTheory RGMISFast
open RootArrivalProfile OrderMixture ArrivalPolynomial FiniteProfileDrift ExponentialArrivals

 theorem root_count_arrival_expansion_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ) (hk : 1 ≤ k)
    (t ρ : ℝ) (ht : 0 < t) (htρ : t ≤ ρ) :
    ∃ (m : ℕ) (coeff : ℕ → ℝ),
      (∀ s ∈ Set.Icc 0 t,
        (∫ r, (Y G u k s r : ℝ) ∂(rootLaw u ρ)) =
          ∑ j ∈ Finset.range (m+1), coeff j * Real.exp (-(j:ℝ)*s)) ∧
      (∀ s ∈ Set.Icc 0 t,
        (∫ r, (dsSum G u k s r : ℝ) ∂(rootLaw u ρ)) =
          ∑ j ∈ Finset.range (m+1), (j:ℝ)*coeff j * Real.exp (-(j:ℝ)*s)) := by
  let n := Fintype.card V
  let e : Fin n ≃ V := (Fintype.equivFin V).symm
  obtain ⟨m,coeff,hf,hd⟩ := exponential_mixture_expansion n (profile e (countProfile G u k))
  refine ⟨m,coeff,?_,?_⟩
  · intro s hs
    rw [count_integral_rootLaw G u k s ρ (hs.2.trans htρ),
      expectation_eq_mixture e (countProfile G u k) (count_prefix_invariant G u k) s hs.1
        (count_integrable G u k s _)]
    exact hf s
  · intro s hs
    rw [loss_integral_rootLaw G u k s ρ (hs.2.trans htρ),
      expectation_eq_mixture e (lossProfile G u k) (loss_prefix_invariant G u k) s hs.1
        (loss_integrable G u k s _),loss_mixture_eq_drift]
    exact hd s

-- Source: Theorems.Thm_RGMISFast_eq_20
open MeasureTheory ProbabilityTheory RGMISFast
theorem RGMISFast.eq_20 {V : Type*} [Fintype V] [LinearOrder V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (hk : 1 ≤ k) (t ρ : ℝ) (ht : 0 < t) (htρ : t ≤ ρ) :
    (∀ s : ℝ, Measurable (fun r : V → ℝ => (Y G u k s r : ℝ))) ∧
    (∀ s : ℝ, Measurable (fun r : V → ℝ => (dsSum G u k s r : ℝ))) ∧
    ∀ s ∈ Set.Ico (0 : ℝ) t,
      HasDerivWithinAt (fun s' : ℝ => ∫ r, (Y G u k s' r : ℝ) ∂(rootLaw u ρ))
        (-(∫ r, (dsSum G u k s r : ℝ) ∂(rootLaw u ρ))) (Set.Icc 0 t) s := by
  refine ⟨?_,?_,?_⟩
  · intro s
    have hm := Y_measurable_complete G u k s
    fun_prop
  · intro s
    have hm := dsSum_measurable_complete G u k s
    fun_prop
  · obtain ⟨n,coeff,hf,hd⟩ := root_count_arrival_expansion_complete G u k hk t ρ ht htρ
    exact derivative_from_arrival_expansion _ _ n coeff t hf hd



-- Source: Solutions.RootCountPinnedBound
open MeasureTheory ProbabilityTheory RGMISFast
namespace RootCountPinnedBound
open Classical RootCountDriftBound RootArrivalProfile
set_option maxHeartbeats 1000000
variable {V : Type*} [Fintype V] [LinearOrder V]
instance root_probability (u : V) (ρ : ℝ) : IsProbabilityMeasure (rootLaw u ρ) := by
  unfold rootLaw
  haveI (v : V) : IsProbabilityMeasure (if v = u then Measure.dirac ρ else expMeasure 1) := by
    split_ifs <;> infer_instance
  infer_instance

lemma pinned_expectation_bound (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (hk : 1 ≤ k) (t : ℝ) (ht : 0 < t) :
    (∫ r, (Y G u k t r : ℝ) ∂rootLaw u t) ≤ (Real.exp 1 / t)^k := by
  let f : ℝ → ℝ := fun s => ∫ r, (Y G u k s r : ℝ) ∂rootLaw u t
  let f' : ℝ → ℝ := fun s => -(∫ r, (dsSum G u k s r : ℝ) ∂rootLaw u t)
  obtain ⟨n,c,hf,hd⟩ := root_count_arrival_expansion_complete G u k hk t t ht le_rfl
  have hc : Continuous (fun s : ℝ => ∑ j ∈ Finset.range (n+1), c j * Real.exp (-(j:ℝ)*s)) := by
    fun_prop
  have hcont : ContinuousOn f (Set.Icc 0 t) := hc.continuousOn.congr hf
  have hnonneg : ∀ s ∈ Set.Icc 0 t, 0 ≤ f s := by
    intro s hs
    exact integral_nonneg (fun r => Nat.cast_nonneg _)
  have hderiv : ∀ s ∈ Set.Ioo 0 t, HasDerivAt f (f' s) s := by
    intro s hs
    exact ((RGMISFast.eq_20 G u k hk t t ht le_rfl).2.2 s ⟨hs.1.le,hs.2⟩).hasDerivAt
      (Icc_mem_nhds hs.1 hs.2)
  have hode : ∀ s ∈ Set.Ioo 0 t,
      f' s ≤ -(k:ℝ)/Real.exp 1 * f s ^ (1+(k:ℝ)⁻¹) := by
    intro s hs
    have hh := expectation_drift_bound G u k hk s (rootLaw u t)
    dsimp [f,f']
    simpa only [neg_div,neg_mul] using neg_le_neg hh
  exact PrescribedDecay.power_decay_bound f f' t k ht hk hcont hnonneg hderiv hode

lemma Y_le_pinned (G : SimpleGraph V) [DecidableRel G.Adj]
    (u : V) (k : ℕ) (s : ℝ) (r : V → ℝ) :
    Y G u k s r ≤ Y G u k s (pin u s r) := by
  by_cases hru : s ≤ r u
  · have he : pin u (r u) r = r := by
      funext v
      by_cases h : v = u <;> simp [pin,h]
    have ha := pinned_activity_congr G u r r s s (r u) s hru le_rfl
      (fun _ => Iff.rfl) (fun _ _ _ _ => Iff.rfl)
    rw [he] at ha
    exact (PrefixOrderActivity.Y_congr G _ _ s s ha u k).le
  · have hz : Y G u k s r = 0 := by
      unfold Y
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      obtain ⟨_,hroot,_,hact⟩ := Finset.mem_filter.mp hA
      exact hru (ArrivalAuxiliary.active_le_rank G r s u (hact u hroot.1))
    rw [hz]
    exact Nat.zero_le _
end RootCountPinnedBound

-- Source: Solutions.CoordinateDisintegration
open MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace CoordinateDisintegration
open Classical
variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def overlay (A : Finset V) (p : (V→ℝ) × (V→ℝ)) : V→ℝ :=
  fun v=>if v∈A then p.1 v else p.2 v
lemma overlay_measurable (A : Finset V) : Measurable (overlay A) := by
  apply measurable_pi_lambda
  intro v
  unfold overlay
  split_ifs <;> fun_prop
lemma overlay_map (μ : V→Measure ℝ) [∀v,IsProbabilityMeasure (μ v)] (A : Finset V) :
    ((Measure.pi μ).prod (Measure.pi μ)).map (overlay A) = Measure.pi μ := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ V
  have he := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ V μ μ).map_eq
  rw [← he,Measure.map_map (overlay_measurable A) e.measurable]
  change (Measure.pi (fun v=>(μ v).prod (μ v))).map
    (fun r v=>if v∈A then (r v).1 else (r v).2) = _
  rw [Measure.pi_map_pi (fun v=>show AEMeasurable (fun p : ℝ×ℝ=>if v∈A then p.1 else p.2) ((μ v).prod (μ v)) from by
    by_cases hv : v∈A <;> simp only [hv,↓reduceIte] <;> fun_prop)]
  congr 1
  funext v
  by_cases hv : v∈A <;> simp [hv]
lemma integral_overlay (μ : V→Measure ℝ) [∀v,IsProbabilityMeasure (μ v)] (A : Finset V)
    (f : (V→ℝ)→ℝ≥0∞) (hf : Measurable f) :
    (∫⁻r,f r ∂Measure.pi μ) = ∫⁻r,∫⁻q,f (overlay A (r,q)) ∂Measure.pi μ ∂Measure.pi μ := by
  calc
    _ = ∫⁻r,f r ∂((Measure.pi μ).prod (Measure.pi μ)).map (overlay A) := by rw [overlay_map]
    _ = _ := by
      rw [lintegral_map hf (overlay_measurable A)]
      exact lintegral_prod _ (hf.comp (overlay_measurable A)).aemeasurable
end CoordinateDisintegration

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

-- Source: Solutions.RootCountUnconditional
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
namespace RootCountUnconditional
open Classical RootArrivalProfile RootCountDriftBound RootCountPinnedBound ExponentialArrivals
variable {V : Type*} [Fintype V] [LinearOrder V]
instance rank_probability : IsProbabilityMeasure (rankLaw V) := by unfold rankLaw; infer_instance
lemma Y_high_pin (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s t : ℝ) (hst : s ≤ t) (r : V→ℝ) (hr : s ≤ r u) :
    Y G u k s r = Y G u k s (pin u t r) := by
  have he : pin u (r u) r=r := by funext v; by_cases hv:v=u <;> simp [pin,hv]
  have ha := pinned_activity_congr G u r r s s (r u) t hr hst (fun _=>Iff.rfl) (fun _ _ _ _=>Iff.rfl)
  rw [he] at ha
  exact PrefixOrderActivity.Y_congr G _ _ s s ha u k
lemma Y_low_zero (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s : ℝ) (r : V→ℝ) (hr : ¬s ≤ r u) : Y G u k s r=0 := by
  unfold Y
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro A hA
  obtain ⟨_,hroot,_,hact⟩ := Finset.mem_filter.mp hA
  exact hr (ArrivalAuxiliary.active_le_rank G r s u (hact u hroot.1))
lemma expectation_factor (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (k : ℕ)
    (s t : ℝ) (hs : 0 ≤ s) (hst : s ≤ t) :
    (∫⁻r,(Y G u k s r:ℝ≥0∞) ∂rankLaw V) =
      ENNReal.ofReal (Real.exp (-s)*(∫r,(Y G u k s r:ℝ) ∂rootLaw u t)) := by
  let μ := rankLaw V
  let g := ∫⁻q,(Y G u k s (pin u t q):ℝ≥0∞) ∂μ
  have hm : Measurable (fun r : V→ℝ=>(Y G u k s r:ℝ≥0∞)) :=
    (measurable_of_countable (fun n : ℕ=>(n:ℝ≥0∞))).comp (Y_measurable_complete G u k s)
  have he (r q : V→ℝ) : (Y G u k s (CoordinateDisintegration.overlay {u} (r,q)):ℝ≥0∞) =
      if s ≤ r u then (Y G u k s (pin u t q):ℝ≥0∞) else 0 := by
    have hv : CoordinateDisintegration.overlay {u} (r,q) u=r u := by simp [CoordinateDisintegration.overlay]
    by_cases hr : s ≤ r u
    · rw [if_pos hr,Y_high_pin G u k s t hst _ (by simpa [hv] using hr)]
      congr 2
      funext v
      by_cases h:v=u <;> simp [pin,CoordinateDisintegration.overlay,h]
    · rw [if_neg hr,Y_low_zero G u k s _ (by simpa [hv] using hr),Nat.cast_zero]
  have hE : MeasurableSet {r : V→ℝ|s ≤ r u} := measurableSet_le measurable_const (measurable_pi_apply u)
  have hprob : μ {r : V→ℝ|s ≤ r u} = ENNReal.ofReal (Real.exp (-s)) := by
    change Measure.pi (fun _ : V=>expMeasure 1) ((fun r=>r u) ⁻¹' Set.Ici s) = _
    rw [← Measure.map_apply (measurable_pi_apply u) measurableSet_Ici,
      (measurePreserving_eval (fun _ : V=>expMeasure 1) u).map_eq]
    exact ConditionalRankBand.exp_tail s hs
  have hg : g=ENNReal.ofReal (∫r,(Y G u k s r:ℝ) ∂rootLaw u t) := by
    have hi := ofReal_integral_eq_lintegral_ofReal (Y_integrable G u k s (rootLaw u t))
      (Filter.Eventually.of_forall (fun r=>Nat.cast_nonneg (Y G u k s r)))
    simp only [ENNReal.ofReal_natCast] at hi
    rw [hi]
    rw [← pin_map,lintegral_map hm (pin_measurable u t)]
    rfl
  rw [show rankLaw V=Measure.pi (fun _ : V=>expMeasure 1) from rfl,
    CoordinateDisintegration.integral_overlay _ {u} _ hm]
  simp_rw [he]
  have hi (r : V→ℝ) : (∫⁻q,if s ≤ r u then (Y G u k s (pin u t q):ℝ≥0∞) else 0 ∂μ)=
      if s ≤ r u then g else 0 := by by_cases hr:s ≤ r u <;> simp [hr,g]
  change (∫⁻r,∫⁻q,if s ≤ r u then (Y G u k s (pin u t q):ℝ≥0∞) else 0 ∂μ ∂μ)=_
  simp_rw [hi]
  change (∫⁻r,({r : V→ℝ|s ≤ r u}.indicator (fun _=>g)) r ∂μ)=_
  rw [lintegral_indicator hE,lintegral_const,Measure.restrict_apply_univ,hprob,hg,←ENNReal.ofReal_mul]
  · congr 1; ring
  · exact integral_nonneg (fun _=>Nat.cast_nonneg _)
end RootCountUnconditional

-- Source: Solutions.RootCountExpectationDriftComplete
open MeasureTheory ProbabilityTheory RGMISFast
open scoped ENNReal
open Classical RootCountUnconditional RootCountPinnedBound RootArrivalProfile RootCountDriftBound
set_option maxHeartbeats 1000000

theorem root_count_expectation_drift_complete {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (t : ℝ) (ht : 0<t)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃f f' : ℝ→ℝ,
      (∀s∈Set.Icc 0 t,(∫⁻r,(Y G u k s r:ℝ≥0∞) ∂rankLaw V)=ENNReal.ofReal (f s)) ∧
      ContinuousOn f (Set.Icc 0 t) ∧ (∀s∈Set.Icc 0 t,0 ≤ f s) ∧
      (∀s∈Set.Ioo 0 t,HasDerivAt f (f' s) s) ∧
      (∀s∈Set.Ioo 0 t,f' s ≤ -(k:ℝ)/Real.exp 1*f s^(1+(k:ℝ)⁻¹)) := by
  let g : ℝ→ℝ := fun s=>∫r,(Y G u k s r:ℝ) ∂rootLaw u t
  let d : ℝ→ℝ := fun s=>∫r,(dsSum G u k s r:ℝ) ∂rootLaw u t
  let f : ℝ→ℝ := fun s=>Real.exp (-s)*g s
  let f' : ℝ→ℝ := fun s=>Real.exp (-s)*(-d s-g s)
  have hg (s : ℝ) : 0 ≤ g s := integral_nonneg (fun _=>Nat.cast_nonneg _)
  obtain ⟨n,c,hpoly,_⟩ := root_count_arrival_expansion_complete G u k hk t t ht le_rfl
  have hcont : ContinuousOn g (Set.Icc 0 t) := by
    have hh : Continuous (fun s : ℝ=>∑j∈Finset.range (n+1),c j*Real.exp (-(j:ℝ)*s)) := by fun_prop
    exact hh.continuousOn.congr hpoly
  refine ⟨f,f',?_,?_,?_,?_,?_⟩
  · intro s hs; exact expectation_factor G u k s t hs.1 hs.2
  · exact (show Continuous (fun s : ℝ=>Real.exp (-s)) by fun_prop).continuousOn.mul hcont
  · intro s _; exact mul_nonneg (Real.exp_pos _).le (hg s)
  · intro s hs
    have hgd : HasDerivAt g (-d s) s :=
      ((RGMISFast.eq_20 G u k hk t t ht le_rfl).2.2 s ⟨hs.1.le,hs.2⟩).hasDerivAt (Icc_mem_nhds hs.1 hs.2)
    have he : HasDerivAt (fun s : ℝ=>Real.exp (-s)) (-Real.exp (-s)) s := by
      convert ((hasDerivAt_id s).neg.exp) using 1 <;> simp
    change HasDerivAt (fun x=>Real.exp (-x)*g x) (Real.exp (-s)*(-d s-g s)) s
    have hdprod := he.mul hgd
    have hcoef : (-Real.exp (-s))*g s+Real.exp (-s)*(-d s)=Real.exp (-s)*(-d s-g s) := by ring
    rw [hcoef] at hdprod
    exact hdprod
  · intro s hs
    have hb := expectation_drift_bound G u k hk s (rootLaw u t)
    change (k:ℝ)/Real.exp 1*(g s)^(1+(k:ℝ)⁻¹) ≤ d s at hb
    have he : Real.exp (-s) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [hs.1])
    have hp : 1 ≤ 1+(k:ℝ)⁻¹ := le_add_of_nonneg_right (inv_nonneg.mpr (Nat.cast_nonneg _))
    have hr : (f s)^(1+(k:ℝ)⁻¹) ≤ Real.exp (-s)*(g s)^(1+(k:ℝ)⁻¹) := by
      dsimp [f]
      rw [Real.mul_rpow (Real.exp_pos _).le (hg s)]
      exact mul_le_mul_of_nonneg_right (Real.rpow_le_self_of_le_one (Real.exp_pos _).le he hp) (Real.rpow_nonneg (hg s) _)
    have h1 := mul_le_mul_of_nonneg_left hb (Real.exp_pos (-s)).le
    have h2 := mul_le_mul_of_nonneg_left hr (show 0 ≤ (k:ℝ)/Real.exp 1 by positivity)
    have h3 := mul_nonneg (Real.exp_pos (-s)).le (hg s)
    have hb2 : (k:ℝ)/Real.exp 1*(f s)^(1+(k:ℝ)⁻¹) ≤ Real.exp (-s)*d s :=
      h2.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using h1)
    change Real.exp (-s)*(-d s-g s) ≤ _
    calc
      _ ≤ -(Real.exp (-s)*d s) := by nlinarith [h3]
      _ ≤ -((k:ℝ)/Real.exp 1*(f s)^(1+(k:ℝ)⁻¹)) := neg_le_neg hb2
      _ = _ := by ring

theorem solution {V : Type*} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (t : ℝ) (ht : 0<t)
    (k : ℕ) (hk : 1 ≤ k) :
    ∃f f' : ℝ→ℝ,
      (∀s∈Set.Icc 0 t,(∫⁻r,(Y G u k s r:ℝ≥0∞) ∂rankLaw V)=ENNReal.ofReal (f s)) ∧
      ContinuousOn f (Set.Icc 0 t) ∧ (∀s∈Set.Icc 0 t,0 ≤ f s) ∧
      (∀s∈Set.Ioo 0 t,HasDerivAt f (f' s) s) ∧
      (∀s∈Set.Ioo 0 t,f' s ≤ -(k:ℝ)/Real.exp 1*f s^(1+(k:ℝ)⁻¹)) := by
  exact root_count_expectation_drift_complete G u t ht k hk

#print axioms solution
