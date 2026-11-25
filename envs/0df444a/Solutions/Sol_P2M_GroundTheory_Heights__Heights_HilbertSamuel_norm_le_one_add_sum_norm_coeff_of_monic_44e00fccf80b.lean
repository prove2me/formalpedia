-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_norm_le_one_add_sum_norm_coeff_of_monic_44e00fccf80b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:28:45.432242+00:00
-- url     : https://prove2.me/submissions/fdb2fee2-e06c-44ec-8066-dd44dd2f86c8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_StMonicRootGrowth
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_IrreducibleConnected_PMonicRootGrowth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial Finset
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {q : Polynomial ℂ} (hq : q.Monic) {τ : ℂ}
    (hτ : q.IsRoot τ) : ‖τ‖ ≤ 1 + ∑ i ∈ range q.natDegree, ‖q.coeff i‖ := by
  have key := hτ.norm_lt_cauchyBound hq.ne_zero
  have hs : Polynomial.cauchyBound q ≤ (∑ i ∈ range q.natDegree, ‖q.coeff i‖₊) + 1 := by
    unfold Polynomial.cauchyBound
    rw [hq.leadingCoeff, nnnorm_one, div_one]
    gcongr
    exact Finset.sup_le fun i hi ↦ single_le_sum (f := fun i ↦ ‖q.coeff i‖₊) (fun _ _ ↦ by positivity) hi
  have h' : ((‖τ‖₊ : NNReal) : ℝ) ≤ (((∑ i ∈ range q.natDegree, ‖q.coeff i‖₊) + 1 : NNReal) : ℝ) :=
    NNReal.coe_le_coe.mpr (key.trans_le hs).le
  push_cast at h'
  linarith
end GroundTheory.Heights₂.Heights.HilbertSamuel
