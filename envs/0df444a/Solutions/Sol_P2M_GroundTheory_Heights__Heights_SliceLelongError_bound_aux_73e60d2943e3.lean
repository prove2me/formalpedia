-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SliceLelongError_bound_aux_73e60d2943e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T05:16:18.414125+00:00
-- url     : https://prove2.me/submissions/f250d8df-e02f-4c68-a70e-1533c568cd36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceLelongError
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceCutChain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceWeightBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StSliceBandEnergy
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSliceLelongError

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
open MvPolynomial Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.SliceLelongError
namespace GroundTheory.Heights₂.Heights.SliceLelongError
theorem _root_.solution {P Q A B k : ℝ} (hk : 0 ≤ k) (hP : |P| ≤ A)
    (hQ : |Q| ≤ B * (2 * (k + 1) - (k + 1) + 1)) :
    |-(k + 1)⁻¹ * P + (k + 1)⁻¹ ^ 2 * Q| ≤ (|A| + 2 * |B|) / (k + 1) := by
  have hk1 : 0 < k + 1 := by linarith
  have ha : 0 < (k + 1)⁻¹ := inv_pos.mpr hk1
  have ha1 : (k + 1)⁻¹ * (k + 1) = 1 := inv_mul_cancel₀ hk1.ne'
  have hale : (k + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith)
  have hP' : |P| ≤ |A| := hP.trans (le_abs_self A)
  have hQ' : |Q| ≤ |B| * (k + 2) := hQ.trans (by
    rw [show 2 * (k + 1) - (k + 1) + 1 = k + 2 by ring]
    exact mul_le_mul_of_nonneg_right (le_abs_self B) (by linarith))
  have key : (k + 1)⁻¹ ^ 2 * (k + 2) ≤ 2 * (k + 1)⁻¹ := by nlinarith
  calc |-(k + 1)⁻¹ * P + (k + 1)⁻¹ ^ 2 * Q|
      ≤ (k + 1)⁻¹ * |P| + (k + 1)⁻¹ ^ 2 * |Q| := by
        refine (abs_add_le _ _).trans (le_of_eq ?_)
        rw [abs_mul, abs_mul, abs_neg, abs_of_pos ha, abs_of_pos (pow_pos ha 2)]
    _ ≤ (k + 1)⁻¹ * |A| + (k + 1)⁻¹ ^ 2 * (|B| * (k + 2)) := by gcongr
    _ ≤ (|A| + 2 * |B|) / (k + 1) := by
        rw [div_eq_mul_inv]
        nlinarith [mul_le_mul_of_nonneg_left key (abs_nonneg B), abs_nonneg A]
end GroundTheory.Heights₂.Heights.SliceLelongError
