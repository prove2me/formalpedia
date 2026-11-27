-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.polar
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:29:45.350466+00:00
-- url     : https://prove2.me/submissions/88487679-cd29-4a8e-86e8-6ca63db1a444

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_PolarBallReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_polar_finrank
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_polar_ballReal
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_I_polar_radial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
universe u
namespace ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Module Set
open scoped ENNReal ContDiff
private theorem nontrivial_V_of_one_le (n : ℕ) (hn : 1 ≤ n) : Nontrivial (ReciprocityTheory.L2DbarEstimates.V n) :=
  Module.nontrivial_of_finrank_pos (R := ℝ) (by rw [polar_finrank]; omega)
end ReciprocityTheory.L2DbarEstimates.I
end

set_option autoImplicit false
universe u
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology Module Set
open scoped ENNReal ContDiff
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution (n : ℕ) : PolarStatement n := by
  intro hn a b ha hab
  have := nontrivial_V_of_one_le n hn
  have hb : 0 < b := ha.trans_le hab
  have hsa0 := Real.sqrt_nonneg a
  have hsb0 := Real.sqrt_nonneg b
  have hsa : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha.le
  have hsb : Real.sqrt b ^ 2 = b := Real.sq_sqrt hb.le
  have hmem : ∀ y : ReciprocityTheory.L2DbarEstimates.V n, (a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b) ↔
      (Real.sqrt a ≤ ‖y‖ ∧ ‖y‖ ≤ Real.sqrt b) := by
    intro y
    have h0 := norm_nonneg y
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · calc Real.sqrt a ≤ Real.sqrt (‖y‖ ^ 2) := Real.sqrt_le_sqrt h1
          _ = ‖y‖ := Real.sqrt_sq h0
      · calc ‖y‖ = Real.sqrt (‖y‖ ^ 2) := (Real.sqrt_sq h0).symm
          _ ≤ Real.sqrt b := Real.sqrt_le_sqrt h2
    · rintro ⟨h1, h2⟩
      exact ⟨by nlinarith, by nlinarith⟩
  have hSc : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} := by
    have h1 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2} :=
      isClosed_le continuous_const (continuous_norm.pow 2)
    have h2 : IsClosed {y : ReciprocityTheory.L2DbarEstimates.V n | ‖y‖ ^ 2 ≤ b} :=
      isClosed_le (continuous_norm.pow 2) continuous_const
    exact h1.inter h2
  have hsub : {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} ⊆ closedBall 0 (b + 1) := by
    intro y hy
    rw [mem_closedBall, dist_zero_right]
    have h0 := norm_nonneg y
    have h2 : ‖y‖ ^ 2 ≤ b := hy.2
    nlinarith [mul_self_nonneg (‖y‖ - 1)]
  have hK : IsCompact {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (isCompact_closedBall (0 : ReciprocityTheory.L2DbarEstimates.V n) (b + 1)).of_isClosed_subset hSc hsub
  have hcont : ContinuousOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} :=
    (continuous_norm.pow 2).continuousOn.rpow_const
      (fun y hy => Or.inl (ha.trans_le (hy : a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b).1).ne')
  have hint_r : IntegrableOn (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ)))
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b} volume :=
    hcont.integrableOn_compact hK
  have hnn : 0 ≤ᵐ[volume.restrict {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}]
      (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) :=
    ae_of_all _ (fun y => Real.rpow_nonneg (by positivity) _)
  rw [← ofReal_integral_eq_lintegral_ofReal hint_r hnn]
  congr 1
  have hpt : ∀ y : ReciprocityTheory.L2DbarEstimates.V n,
      {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}.indicator
          (fun y : ReciprocityTheory.L2DbarEstimates.V n => (‖y‖ ^ 2) ^ (-(n : ℝ))) y =
        (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    intro y
    classical
    rw [Set.indicator_apply, Set.indicator_apply]
    by_cases hy : y ∈ {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}
    · rw [if_pos hy, if_pos (show ‖y‖ ∈ Icc (Real.sqrt a) (Real.sqrt b) from (hmem y).1 hy)]
    · rw [if_neg hy, if_neg (show ‖y‖ ∉ Icc (Real.sqrt a) (Real.sqrt b) from
        fun h => hy ((hmem y).2 h))]
  have hI : ∫ y in {y : ReciprocityTheory.L2DbarEstimates.V n | a ≤ ‖y‖ ^ 2 ∧ ‖y‖ ^ 2 ≤ b}, (‖y‖ ^ 2) ^ (-(n : ℝ)) =
      ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ := by
    rw [← integral_indicator hSc.measurableSet]
    exact congrArg _ (funext hpt)
  have hP : ∫ y : ReciprocityTheory.L2DbarEstimates.V n, (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) ‖y‖ =
      (2 * n : ℕ) • (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)).real (ball 0 1) • ∫ y in Ioi (0:ℝ),
        y ^ (2 * n - 1) • (Icc (Real.sqrt a) (Real.sqrt b)).indicator (fun t : ℝ => (t ^ 2) ^ (-(n : ℝ))) y := by
    rw [integral_fun_norm_addHaar (volume : Measure (ReciprocityTheory.L2DbarEstimates.V n)), polar_finrank]
  rw [hI, hP, polar_ballReal n hn, polar_radial n hn a b ha hab,
    nsmul_eq_mul, smul_eq_mul]
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
  rw [Nat.add_sub_cancel, Nat.factorial_succ]
  push_cast
  have hk : (k.factorial : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  field_simp
end ReciprocityTheory.L2DbarEstimates.I
