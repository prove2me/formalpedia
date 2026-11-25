-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_metricDefect_smul_885c138dceb0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:35:59.398726+00:00
-- url     : https://prove2.me/submissions/115900e0-3c8a-4efd-a355-892539b90521

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_Comparison

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
omit [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (A : HermLine n) (c : ι → ℂ) (z : Cone n ℂ) (hc : ∀ k, c k ≠ 0)
    (hz : BlockNonzero z) :
    metricDefect A (fun k i ↦ c k * z k i) = metricDefect A z := by
  have hcn : ∀ k, 0 < ‖c k‖ := fun k ↦ norm_pos_iff.mpr (hc k)
  have hl : ∀ k, 0 < l2Norm (z k) := fun k ↦ vectorL2Norm_pos (hz k)
  unfold metricDefect
  rw [A.metric_smul c z hc hz, Real.log_mul (Finset.prod_pos fun k _ ↦ zpow_pos (hcn k) _).ne'
    (A.metric_pos z hz).ne', Real.log_prod (fun k _ ↦ (zpow_pos (hcn k) _).ne')]
  have e : ∀ k, l2Norm (fun i ↦ c k * z k i) = ‖c k‖ * l2Norm (z k) := fun k ↦ vectorL2Norm_const_mul _ _
  simp only [e, Real.log_zpow]
  simp only [show ∀ k, Real.log (‖c k‖ * l2Norm (z k)) = Real.log ‖c k‖ + Real.log (l2Norm (z k)) from
    fun k ↦ Real.log_mul (hcn k).ne' (hl k).ne']
  simp only [mul_add, Finset.sum_add_distrib]
  ring
end GroundTheory.Heights₂.Heights
