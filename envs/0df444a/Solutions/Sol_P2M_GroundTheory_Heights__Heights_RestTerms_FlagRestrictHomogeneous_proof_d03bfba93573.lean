-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_FlagRestrictHomogeneous_proof_d03bfba93573
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:10:26.0346+00:00
-- url     : https://prove2.me/submissions/b9b14954-d89d-4837-a92d-163d51a0692c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsFlag
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PFlagRestrictHomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace FlagRestrictHomogeneous
theorem _root_.solution : FlagRestrictHomogeneous.Statement := by
  intro f N τ R k hR
  have h := hR.aeval (fun p : Fin f × Fin N => if p.1 = τ then X p.2 else 0) (n := 1) (by
    intro p
    split_ifs
    · exact isHomogeneous_X ℚ _
    · exact isHomogeneous_zero _ _ _)
  rw [one_mul] at h
  exact h
end FlagRestrictHomogeneous
end GroundTheory.Heights₂.Heights.RestTerms
