-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagDividedDifferencePoly_proof_3abd6819389b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:14:23.783583+00:00
-- url     : https://prove2.me/submissions/0a4a8707-cd06-47fe-ab1f-aedbe1c3fc47

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagDividedDifferencePoly
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockPermute_blockVandermonde_69995dfc062e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockSign_mul_self_a12250e20b18
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Flag_blockVandermonde_ne_zero_737fbd71d1a2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_isBlockAlternating_antisymmetrize_1230b0a0ab9c


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
open GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagDividedDifferencePoly
theorem _root_.solution (h1 : FlagVandermondeDvd.Statement) :
    FlagDividedDifferencePoly.Statement := by
  intro f N H
  obtain ⟨R, hR⟩ := h1 f N _ (isBlockAlternating_antisymmetrize f N H)
  refine ⟨R, hR, fun w => ?_⟩
  have h := isBlockAlternating_antisymmetrize f N H w
  rw [hR, map_mul, Flag.blockPermute_blockVandermonde, smul_mul_assoc] at h
  have hs : blockSign f N w ≠ 0 := by
    intro h0
    have := Flag.blockSign_mul_self f N w
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  exact mul_left_cancel₀ (Flag.blockVandermonde_ne_zero f N) (smul_right_injective _ hs h)
end FlagDividedDifferencePoly
end GroundTheory.Heights₂.Heights.RestTerms
