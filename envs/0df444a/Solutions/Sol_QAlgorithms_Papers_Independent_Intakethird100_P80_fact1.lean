-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Intakethird100.P80.fact1
-- status  : ACCEPTED   (prove)
-- author  : @vibe-prover
-- created : 2026-11-10T10:04:10.317628+00:00
-- url     : https://prove2.me/submissions/69e15c62-32d6-48c7-acae-c93f0dd1386a

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp
import Definitions.Def_QAlgorithms_Papers_Independent_Intakethird100_P80
import Mathlib.Algebra.BigOperators.Fin

/-! Statistical strength: ordering and strict positivity for the exact published model. -/

set_option autoImplicit false

namespace S04P055Probe

/-- The scalar inequality needed for a continuous Hellinger lower bound on KL.
This inequality is used in the full P055 proof below. -/
theorem scalar_hellinger_bound {q p : ℝ} (hq : 0 < q) (hp : 0 < p) :
    2 * (q - Real.sqrt q * Real.sqrt p) ≤ q * Real.log (q / p) := by
  have hs_q : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  have hs_p : 0 < Real.sqrt p := Real.sqrt_pos.2 hp
  have hl := Real.log_le_sub_one_of_pos (div_pos hs_p hs_q)
  have hl' := mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * q)
  have hlog : Real.log (q / p) = -2 * Real.log (Real.sqrt p / Real.sqrt q) := by
    rw [Real.log_div hq.ne' hp.ne', Real.log_div hs_p.ne' hs_q.ne',
      Real.log_sqrt hp.le, Real.log_sqrt hq.le]
    ring
  have hmul : q * (Real.sqrt p / Real.sqrt q) = Real.sqrt q * Real.sqrt p := by
    calc
      q * (Real.sqrt p / Real.sqrt q) =
          (Real.sqrt q * Real.sqrt q) * (Real.sqrt p / Real.sqrt q) := by
            rw [Real.mul_self_sqrt hq.le]
      _ = Real.sqrt q * Real.sqrt p := by field_simp [hs_q.ne']
  rw [hlog]
  nlinarith

/-- The exact finite analytic core. A support mismatch will be handled by the
published KL definition's infinity branch, before applying this lemma. -/
theorem finite_hellinger_bound {I : Type*} [Fintype I] (q p : I → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i)
    (hqsum : ∑ i, q i = 1) (hpsum : ∑ i, p i = 1)
    (hdom : ∀ i, 0 < q i → 0 < p i) :
    (∑ i, (Real.sqrt (q i) - Real.sqrt (p i)) ^ 2) ≤
      ∑ i, if q i = 0 then 0 else q i * Real.log (q i / p i) := by
  classical
  have hterm : ∀ i, 2 * (q i - Real.sqrt (q i) * Real.sqrt (p i)) ≤
      if q i = 0 then 0 else q i * Real.log (q i / p i) := by
    intro i
    by_cases hi : q i = 0
    · simp [hi]
    · rw [if_neg hi]
      have hqi : 0 < q i := lt_of_le_of_ne (hq i) (Ne.symm hi)
      exact scalar_hellinger_bound hqi (hdom i hqi)
  have hid : (∑ i, (Real.sqrt (q i) - Real.sqrt (p i)) ^ 2) =
      ∑ i, 2 * (q i - Real.sqrt (q i) * Real.sqrt (p i)) := by
    calc
      _ = (∑ i, 2 * (q i - Real.sqrt (q i) * Real.sqrt (p i))) +
          ∑ i, (p i - q i) := by
            rw [← Finset.sum_add_distrib]
            apply Finset.sum_congr rfl
            intro i _
            nlinarith [Real.sq_sqrt (hq i), Real.sq_sqrt (hp i)]
      _ = _ := by rw [Finset.sum_sub_distrib, hqsum, hpsum]; ring
  rw [hid]
  exact Finset.sum_le_sum fun i _ => hterm i

theorem hellinger_zero_iff {I : Type*} [Fintype I] (q p : I → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i) :
    (∑ i, (Real.sqrt (q i) - Real.sqrt (p i)) ^ 2) = 0 ↔ q = p := by
  classical
  constructor
  · intro h
    funext i
    have hi : (Real.sqrt (q i) - Real.sqrt (p i)) ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg _)).mp h i (Finset.mem_univ i)
    have he : Real.sqrt (q i) = Real.sqrt (p i) :=
      sub_eq_zero.mp (sq_eq_zero_iff.mp hi)
    calc
      q i = (Real.sqrt (q i)) ^ 2 := (Real.sq_sqrt (hq i)).symm
      _ = (Real.sqrt (p i)) ^ 2 := by rw [he]
      _ = p i := Real.sq_sqrt (hp i)
  · rintro rfl
    simp

theorem finite_hellinger_bound_bits {I : Type*} [Fintype I] (q p : I → ℝ)
    (hq : ∀ i, 0 ≤ q i) (hp : ∀ i, 0 ≤ p i)
    (hqsum : ∑ i, q i = 1) (hpsum : ∑ i, p i = 1)
    (hdom : ∀ i, 0 < q i → 0 < p i) :
    (∑ i, (Real.sqrt (q i) - Real.sqrt (p i)) ^ 2) / Real.log 2 ≤
      ∑ i, if q i = 0 then 0 else q i * Real.logb 2 (q i / p i) := by
  classical
  have hb := div_le_div_of_nonneg_right
    (finite_hellinger_bound q p hq hp hqsum hpsum hdom)
    (le_of_lt (Real.log_pos (by norm_num : (1 : ℝ) < 2)))
  simpa only [Finset.sum_div, ite_div, zero_div, Real.logb, mul_div_assoc] using hb

theorem continuous_hellinger {I : Type*} [Fintype I] (q : I → ℝ) :
    Continuous (fun p : I → ℝ => ∑ i, (Real.sqrt (q i) - Real.sqrt (p i)) ^ 2) := by
  fun_prop

/-- Compact separation uses a continuous finite surrogate and avoids lower
semicontinuity of the extended-real KL divergence. -/
theorem compact_hellinger_gap {X I : Type*} [TopologicalSpace X] [Fintype I]
    (q : I → ℝ) (p : X → I → ℝ) (K : Set X) (hK : IsCompact K)
    (hc : ContinuousOn p K) (hq : ∀ i, 0 ≤ q i)
    (hp : ∀ x ∈ K, ∀ i, 0 ≤ p x i) (hne : ∀ x ∈ K, q ≠ p x) :
    ∃ c : ℝ, 0 < c ∧
      ∀ x ∈ K, c ≤ ∑ i, (Real.sqrt (q i) - Real.sqrt (p x i)) ^ 2 := by
  apply hK.exists_forall_le'
  · exact (continuous_hellinger q).comp_continuousOn hc
  · intro x hx
    apply lt_of_le_of_ne (Finset.sum_nonneg (fun i _ => sq_nonneg _))
    intro hzero
    exact hne x hx ((hellinger_zero_iff q (p x) hq (hp x hx)).mp hzero.symm)


end S04P055Probe

set_option autoImplicit false

noncomputable section

open scoped BigOperators ENNReal
open QAlgorithms.Papers.Independent.Intakethird100.P80

namespace S04P055

instance instNonemptySettings (S : BellExperiment) : Nonempty (Settings S) :=
  ⟨fun i => ⟨0, S.settings_pos i⟩⟩

instance instNonemptyPotential (S : BellExperiment) : Nonempty (Potential S) :=
  ⟨fun i a => ⟨0, S.outcomes_pos i a⟩⟩

instance instNonemptyMeasuredOutcomes (S : BellExperiment) (s : Settings S) :
    Nonempty (MeasuredOutcomes S s) :=
  ⟨fun i => ⟨0, S.outcomes_pos i (s i)⟩⟩

theorem uniformSettings_mem (S : BellExperiment) :
    uniformSettings S ∈ stdSimplex ℝ (Settings S) := by
  exact (stdSimplex.barycenter : stdSimplex ℝ (Settings S)).property

theorem uniformSettings_pos (S : BellExperiment) (s : Settings S) :
    0 < uniformSettings S s := by
  unfold uniformSettings
  exact inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)

theorem uniformSettings_uncorrelated (S : BellExperiment) :
    Uncorrelated (uniformSettings S) := by
  classical
  let : ∀ i : Fin S.parties, Nonempty (Fin (S.settings i)) :=
    fun i => ⟨⟨0, S.settings_pos i⟩⟩
  refine ⟨fun i => (stdSimplex.barycenter : stdSimplex ℝ (Fin (S.settings i))), ?_⟩
  intro a
  simp [uniformSettings, Settings, Fintype.card_pi, Finset.prod_inv_distrib,
    Nat.cast_prod]

theorem localTable_mem {S : BellExperiment} (p : PiLocal S) (s : Settings S) :
    localTable p.1 s ∈ stdSimplex ℝ (MeasuredOutcomes S s) := by
  classical
  constructor
  · intro x
    unfold localTable
    apply Finset.sum_nonneg
    intro v hv
    split_ifs
    · exact p.property.1 v
    · exact le_rfl
  · change (∑ x, ∑ v, if potentialAtSetting v s = x then p.1 v else 0) = 1
    rw [Finset.sum_comm]
    simpa using p.property.2

theorem trialJointLaw_mem {S : BellExperiment} (Q : Table S)
    (hQ : ∀ a, Q a ∈ stdSimplex ℝ (MeasuredOutcomes S a)) (s : Sigma S) :
    trialJointLaw Q s.1 ∈ stdSimplex ℝ (BellTrial S) := by
  constructor
  · intro z
    exact mul_nonneg (s.property.1 z.1) ((hQ z.1).1 z.2)
  · simpa only [trialJointLaw, Fintype.sum_sigma, ← Finset.mul_sum,
      fun a => (hQ a).2, mul_one] using s.property.2

theorem uniform_le_uncorrelated {S : BellExperiment} (Q : Table S) :
    uniformStrength Q ≤ uncorrelatedStrength Q := by
  unfold uniformStrength uncorrelatedStrength
  exact le_iSup_of_le
    ⟨⟨uniformSettings S, uniformSettings_mem S⟩, uniformSettings_uncorrelated S⟩ le_rfl

theorem uncorrelated_le_correlated {S : BellExperiment} (Q : Table S) :
    uncorrelatedStrength Q ≤ correlatedStrength Q := by
  unfold uncorrelatedStrength correlatedStrength
  apply iSup_le
  intro s
  exact le_iSup_of_le s.val le_rfl

theorem kl_self {I : Type*} [Fintype I] (q : I → ℝ) : kl q q = 0 := by
  classical
  have hsupport : ¬ ∃ x, 0 < q x ∧ q x = 0 := by
    rintro ⟨x, hx, hzero⟩
    exact (ne_of_gt hx) hzero
  have hsum : (∑ x, if q x = 0 then 0 else q x * Real.logb 2 (q x / q x)) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hzero : q x = 0 <;> simp [hzero]
  simp [kl, hsupport, hsum]

theorem uniformStrength_eq_zero_of_notProper {S : BellExperiment} (Q : Table S)
    (h : ¬ Proper Q) : uniformStrength Q = 0 := by
  classical
  have hlocal : ∃ p : PiLocal S, localTable p.1 = Q := by
    simpa [Proper] using h
  obtain ⟨p, hp⟩ := hlocal
  apply le_antisymm ?_ zero_le
  unfold uniformStrength lowerValue
  apply iInf_le_of_le p
  simp [statisticalPayoff, hp, kl_self]

theorem proper_of_uniformStrength_pos {S : BellExperiment} (Q : Table S)
    (h : 0 < uniformStrength Q) : Proper Q := by
  by_contra hn
  rw [uniformStrength_eq_zero_of_notProper Q hn] at h
  exact (lt_irrefl 0) h

end S04P055

set_option autoImplicit false

noncomputable section

namespace S04P055

open QAlgorithms.Papers.Independent.Intakethird100.P80
open scoped BigOperators ENNReal

/-- The exact published KL dominates a continuous distance between finite laws.
The infinity branch covers every support mismatch. -/
theorem kl_lower_bound {I : Type*} [Fintype I] (q p : I → ℝ)
    (hq : q ∈ stdSimplex ℝ I) (hp : p ∈ stdSimplex ℝ I) :
    ENNReal.ofReal ((∑ i, (Real.sqrt (q i) - Real.sqrt (p i)) ^ 2) / Real.log 2)
      ≤ kl q p := by
  classical
  unfold kl
  split_ifs with hs
  · exact le_top
  · apply ENNReal.ofReal_le_ofReal
    apply S04P055Probe.finite_hellinger_bound_bits q p hq.1 hp.1 hq.2 hp.2
    intro i hqi
    apply lt_of_le_of_ne (hp.1 i)
    intro hpi
    exact hs ⟨i, hqi, hpi.symm⟩

theorem continuous_localTable {S : BellExperiment}
    (s : Settings S) (x : MeasuredOutcomes S s) :
    Continuous (fun p : Potential S → ℝ => localTable p s x) := by
  classical
  unfold localTable
  apply continuous_finsetSum
  intro v _
  split_ifs <;> fun_prop

theorem continuous_localJoint (S : BellExperiment) :
    Continuous (fun p : Potential S → ℝ =>
      trialJointLaw (localTable p) (uniformSettings S)) := by
  apply continuous_pi
  intro z
  change Continuous (fun p : Potential S → ℝ =>
    uniformSettings S z.1 * localTable p z.1 z.2)
  exact continuous_const.mul (continuous_localTable z.1 z.2)

/-- Properness gives a positive uniform statistical strength. Only the finite
probability-law part of the experiment assumptions is needed. -/
theorem uniformStrength_pos_of_proper {S : BellExperiment} (Q : Table S)
    (hQ : ∀ s, Q s ∈ stdSimplex ℝ (MeasuredOutcomes S s)) (hproper : Proper Q) :
    0 < uniformStrength Q := by
  classical
  let sigma : Sigma S := ⟨uniformSettings S, uniformSettings_mem S⟩
  let q : BellTrial S → ℝ := trialJointLaw Q (uniformSettings S)
  let P : (Potential S → ℝ) → BellTrial S → ℝ :=
    fun p => trialJointLaw (localTable p) (uniformSettings S)
  have hq : q ∈ stdSimplex ℝ (BellTrial S) := trialJointLaw_mem Q hQ sigma
  have hp (p : PiLocal S) : P p.1 ∈ stdSimplex ℝ (BellTrial S) :=
    trialJointLaw_mem (localTable p.1) (localTable_mem p) sigma
  have hneq : ∀ p ∈ stdSimplex ℝ (Potential S), q ≠ P p := by
    intro p hpmem heq
    apply hproper
    refine ⟨⟨p, hpmem⟩, ?_⟩
    funext s x
    have he := congrFun heq ⟨s, x⟩
    change uniformSettings S s * Q s x = uniformSettings S s * localTable p s x at he
    exact (mul_left_cancel₀ (uniformSettings_pos S s).ne' he).symm
  obtain ⟨c, hc, hgap⟩ := S04P055Probe.compact_hellinger_gap q P
    (stdSimplex ℝ (Potential S)) (isCompact_stdSimplex ℝ (Potential S))
    (continuous_localJoint S).continuousOn hq.1
    (fun p hp' => (hp ⟨p, hp'⟩).1) hneq
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hc' : 0 < ENNReal.ofReal (c / Real.log 2) :=
    ENNReal.ofReal_pos.mpr (div_pos hc hlog)
  apply lt_of_lt_of_le hc'
  change ENNReal.ofReal (c / Real.log 2) ≤ ⨅ p : PiLocal S, kl q (P p.1)
  apply le_iInf
  intro p
  calc
    ENNReal.ofReal (c / Real.log 2) ≤
        ENNReal.ofReal ((∑ i, (Real.sqrt (q i) - Real.sqrt (P p.1 i)) ^ 2) /
          Real.log 2) := by
      exact ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (hgap p.1 p.2) hlog.le)
    _ ≤ kl q (P p.1) := kl_lower_bound q (P p.1) hq (hp p)


end S04P055

set_option autoImplicit false

open QAlgorithms.Papers.Independent.Intakethird100.P80

theorem solution {S : BellExperiment} (Q : Table S) (hQ : NonlocalityProof Q) :
    uniformStrength Q ≤ uncorrelatedStrength Q ∧
    uncorrelatedStrength Q ≤ correlatedStrength Q ∧
    (0 < uniformStrength Q ↔ Proper Q) := by
  exact ⟨S04P055.uniform_le_uncorrelated Q, S04P055.uncorrelated_le_correlated Q,
    ⟨S04P055.proper_of_uniformStrength_pos Q,
      S04P055.uniformStrength_pos_of_proper Q hQ.1⟩⟩

#print axioms solution
