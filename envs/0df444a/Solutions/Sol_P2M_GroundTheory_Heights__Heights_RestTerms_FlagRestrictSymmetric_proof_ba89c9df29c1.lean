-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagRestrictSymmetric_proof_ba89c9df29c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:27:38.829249+00:00
-- url     : https://prove2.me/submissions/0f3ffdf0-6883-4ebf-8823-6814568f59cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagRestrictSymmetric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_rename_comp_restrictToBlock_ce0769050c98

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
namespace FlagRestrictSymmetric
theorem _root_.solution : FlagRestrictSymmetric.Statement := by
  intro f N τ R hR π
  have key := congrArg (fun φ : RootRing f N →ₐ[ℚ] MvPolynomial (Fin N) ℚ => φ R)
    (rename_comp_restrictToBlock f N τ π)
  simp only [AlgHom.comp_apply] at key
  rw [key, hR]
end FlagRestrictSymmetric
end GroundTheory.Heights₂.Heights.RestTerms
