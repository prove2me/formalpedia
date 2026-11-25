-- Prove2me | solution 1 for PositivityTheory.RL.Up.seminorm_succ_k
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:28:52.102799+00:00
-- url     : https://prove2.me/submissions/20c35004-8713-468c-ac35-4496a059c261

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RealMetaplecticRepresentation
import Definitions.Def_Development_WeilBound_CoreStatements_GaussianSeminormBounds_RealSeminormFiltration_RLLieA
import Theorems.Thm_GlobalTheory_RealWeil_dRho_single_inr


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix Filter Topology Asymptotics
open scoped Real RealInnerProductSpace ContDiff
open PositivityTheory PositivityTheory.RL PositivityTheory.RL.Up
open GlobalTheory.RealWeil
variable {l : Type} [Fintype l] [DecidableEq l]
namespace PositivityTheory.RL.Up
theorem _root_.solution (k : ℕ) (g : Sch l) :
    SchwartzMap.seminorm ℂ (k + 1) 0 g ≤ ∑ i, SchwartzMap.seminorm ℂ k 0 (dRho (Pi.single (Sum.inr i) 1) g) := by
  refine SchwartzMap.seminorm_le_bound ℂ (k + 1) 0 g (Finset.sum_nonneg fun _ _ => apply_nonneg _ _) fun x => ?_
  have h1 : ‖x‖ ≤ ∑ i, |x i| := by
    have hv : x = ∑ i, x i • (EuclideanSpace.single i 1 : EuclideanSpace ℝ l) := by
      ext j
      simp [Pi.single_apply]
    conv_lhs => rw [hv]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    simp [norm_smul]
  rw [norm_iteratedFDeriv_zero]
  calc ‖x‖ ^ (k + 1) * ‖g x‖ = ‖x‖ * (‖x‖ ^ k * ‖g x‖) := by ring
    _ ≤ (∑ i, |x i|) * (‖x‖ ^ k * ‖g x‖) := mul_le_mul_of_nonneg_right h1 (by positivity)
    _ ≤ _ := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => le_trans ?_ (SchwartzMap.le_seminorm ℂ k 0 _ x)
      rw [norm_iteratedFDeriv_zero, dRho_single_inr]
      simp only [norm_mul, norm_ofNat, norm_real, norm_I, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
      have : |x i| * (‖x‖ ^ k * ‖g x‖) * 1 ≤ |x i| * (‖x‖ ^ k * ‖g x‖) * (2 * π) :=
        mul_le_mul_of_nonneg_left (by linarith [Real.pi_gt_three]) (by positivity)
      linarith
end PositivityTheory.RL.Up
