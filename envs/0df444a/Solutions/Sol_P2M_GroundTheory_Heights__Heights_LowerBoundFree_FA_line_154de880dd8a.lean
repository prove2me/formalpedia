-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FA_line_154de880dd8a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:03:44.698047+00:00
-- url     : https://prove2.me/submissions/c95ed531-12a8-439c-bec1-87827c47cdd0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_dimN_line_500fcd94b89b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_muPoly_line_d486cf876662
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_vandBlocks_line_0cdaf03e7255

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution (cf : ℚ) : FA Unit 2 1 cf = C cf * X ((), 1) ^ 2 := by
  unfold FA fib
  rw [dimN_line, muPoly_line, vandBlocks_line]
  ring
end GroundTheory.Heights₂.Heights.LowerBoundFree
