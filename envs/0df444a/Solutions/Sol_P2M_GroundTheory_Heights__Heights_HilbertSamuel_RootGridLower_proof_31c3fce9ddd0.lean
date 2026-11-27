-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_proof_31c3fce9ddd0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:57:34.274384+00:00
-- url     : https://prove2.me/submissions/da5c9790-401d-41b0-a23d-9d878ed9fd05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsRootGridLower
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PRootGridLower
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_RootGridLower_of_pos_62bab9c7db63

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
namespace RootGridLower
theorem _root_.solution : RootGridLower.Statement := by
  intro e m Q hQ hdeg
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · obtain ⟨ζ, -, hζ⟩ := RootGridLower.of_pos Nat.one_pos Q hQ
      (fun i => lt_trans (hdeg i) Nat.one_pos)
    exact ⟨ζ, fun i => pow_zero _, hζ⟩
  · exact RootGridLower.of_pos hm Q hQ hdeg
end RootGridLower
end GroundTheory.Heights₂.Heights.HilbertSamuel
