-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_zero_finite_acc1125a749b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T04:45:25.006188+00:00
-- url     : https://prove2.me/submissions/0387b4d7-6185-4156-b8fc-30e92736500f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_RigSymFormTauINontrivial
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ThetaKeyFormula_ThetaThreeFamLinearIndependent
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_differentiable_56fbb8528aea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_int_mul_I_ff45644aceb5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_add_int_5b4389eedbd1
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KeyFormula_thetaThree_ne_zero_f16649ac4b2d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.KeyFormula
open Complex Real MeasureTheory intervalIntegral Matrix
noncomputable section
namespace GroundTheory.Heights₂.Heights.KeyFormula
theorem _root_.solution :
    ∃ W : Finset ℂ, ∀ w, thetaThree 0 w = 0 → ∃ w' ∈ W, ∃ m k : ℤ, w = w' + k * I + m := by
  set S : Set ℂ := {w | w ∈ Metric.closedBall (0 : ℂ) 2 ∧ thetaThree 0 w = 0} with hS
  have hSfin : S.Finite := by
    by_contra hinf
    obtain ⟨x, -, hx⟩ := Set.Infinite.exists_accPt_of_subset_isCompact hinf
      (isCompact_closedBall (0 : ℂ) 2) (fun w hw => hw.1)
    rw [accPt_iff_frequently_nhdsNE] at hx
    have han : AnalyticOnNhd ℂ (thetaThree 0) Set.univ :=
      fun z _ => (thetaThree_differentiable 0).analyticAt z
    have := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (Set.mem_univ x) (hx.mono fun w hw => hw.2)
    obtain ⟨w, hw⟩ := thetaThree_ne_zero 0
    exact hw (this (Set.mem_univ w))
  refine ⟨hSfin.toFinset, fun w hw => ?_⟩
  set m := ⌊w.re⌋ with hm
  set k := ⌊w.im⌋ with hk
  set w' : ℂ := w - k * I - m with hw'
  have hshift : thetaThree 0 w = cexp (-(3 * π * I * k ^ 2 * I) - 6 * π * I * k * (w' + m)) *
      thetaThree 0 w' := by
    have e : w = (w' + m) + k * I := by rw [hw']; ring
    rw [e, thetaThree_add_int_mul_I, thetaThree_add_int]
  have hz' : thetaThree 0 w' = 0 := by
    rw [hshift] at hw
    exact (mul_eq_zero.mp hw).resolve_left (Complex.exp_ne_zero _)
  have hre : w'.re = Int.fract w.re := by rw [← Int.self_sub_floor]; simp [hw', hm]
  have him : w'.im = Int.fract w.im := by rw [← Int.self_sub_floor]; simp [hw', hk]
  have hball : w' ∈ Metric.closedBall (0 : ℂ) 2 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖w'‖ ≤ |w'.re| + |w'.im| := Complex.norm_le_abs_re_add_abs_im w'
      _ ≤ 1 + 1 := by
        rw [hre, him]
        gcongr
        · rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le
        · rw [abs_of_nonneg (Int.fract_nonneg _)]; exact (Int.fract_lt_one _).le
      _ = 2 := by norm_num
  refine ⟨w', hSfin.mem_toFinset.mpr ⟨hball, hz'⟩, m, k, ?_⟩
  rw [hw']; ring
end GroundTheory.Heights₂.Heights.KeyFormula
