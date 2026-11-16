-- Prove2me | solution 2 for RGMISFast.lemma_A_2
-- status  : ACCEPTED   (prove)
-- author  : @srikkanthr
-- created : 2026-11-16T05:48:53.825117+00:00
-- url     : https://prove2.me/submissions/57ae4354-1ebd-4a61-983c-7157e9cd425c

import Definitions.Def_RGMISFast_IsRootConnected
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

theorem family_large_pos (G : SimpleGraph V) [DecidableRel G.Adj] (u : V)
    (F : Finset (Finset V)) (k Δ : ℕ) (hΔ : 1 ≤ Δ) (hk3 : 3 ≤ k)
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
  have hΔreal : (1 : ℝ) ≤ Δ := by exact_mod_cast hΔ
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



lemma count_bound_pos (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (n Δ : ℕ)
    (hΔ : 1 ≤ Δ) (hd : ∀v,G.degree v ≤ Δ) : (sets G u n).card ≤ (4*Δ)^n := by
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
    apply family_large_pos G u F n Δ hΔ hn hd
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
lemma count_bound (G : SimpleGraph V) [DecidableRel G.Adj] (u : V) (n Δ : ℕ)
    (hΔ : 2 ≤ Δ) (hd : ∀v,G.degree v ≤ Δ) : (sets G u n).card ≤ (4*Δ)^n :=
  count_bound_pos G u n Δ (by omega) hd
end LowRankCounting

-- Source: Solutions.LemmaA2Complete
open RGMISFast
open Classical LowRankCounting RGMISGeneral.Polynomial

theorem lemma_A_2_complete {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hdeg : ∀v,G.degree v ≤ Δ) (u : V) (j : ℕ) :
    {A : Finset V|IsRootConnected G u A ∧ A.card=j+1}.ncard ≤ (4*Δ)^j := by
  have hs : {A : Finset V|IsRootConnected G u A ∧ A.card=j+1} ⊆ (sets G u j : Set (Finset V)) := by
    intro A hA
    apply (mem_sets G u j A).mpr
    refine ⟨⟨hA.1.1,?_⟩,hA.2⟩
    intro v hv
    have hp := (SimpleGraph.reachable_iff_reflTransGen ..).mp (hA.1.2 v hv)
    clear hv
    induction hp with
    | refl => exact .refl
    | tail _ h ih => exact ih.tail ⟨h.1,h.2.2⟩
  have hb : (sets G u j).card ≤ (4*Δ)^j := by
    by_cases hd : 1 ≤ Δ
    · exact count_bound_pos G u j Δ hd hdeg
    · have he : Δ=0 := by omega
      subst Δ
      cases j with
      | zero => simpa using count_zero G u
      | succ n => simpa using count_succ G u n 0 hdeg
  exact (Set.ncard_le_ncard hs).trans ((Set.ncard_coe_finset _).le.trans hb)

theorem solution {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (Δ : ℕ) (hdeg : ∀v,G.degree v ≤ Δ) (u : V) (j : ℕ) :
    {A : Finset V|IsRootConnected G u A ∧ A.card=j+1}.ncard ≤ (4*Δ)^j := by
  exact lemma_A_2_complete G Δ hdeg u j

#print axioms solution
