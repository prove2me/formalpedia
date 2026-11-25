-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PlueckerUnitBound_proof_304254eb0cde
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:54:51.723284+00:00
-- url     : https://prove2.me/submissions/6d2ec49e-6b6d-49d3-9ef9-6d43fab2661b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsGrass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PPlueckerUnitBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_posSemidef_one_add_2384f25ff10d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PlueckerUnitBoundAlt_diag_eq_1542fd0d2644

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
open Matrix Finset
open scoped ComplexOrder
open PlueckerUnitBoundAlt
namespace GroundTheory.Heights₂.Heights
namespace PlueckerUnitBound
theorem _root_.solution (h : HadamardPSD.Statement) : PlueckerUnitBound.Statement := by
  intro j m Z hZ
  calc ‖(1 + Z * Zᴴ).det‖ ≤ ∏ a, ‖(1 + Z * Zᴴ : Matrix (Fin j) (Fin j) ℂ) a a‖ := h j _ (posSemidef_one_add Z)
    _ = ∏ _a : Fin j, (1 + m : ℝ) := by
        refine Finset.prod_congr rfl fun a _ => ?_
        rw [diag_eq Z hZ a, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    _ = (1 + m : ℝ) ^ j := by
        rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
end PlueckerUnitBound
end GroundTheory.Heights₂.Heights
