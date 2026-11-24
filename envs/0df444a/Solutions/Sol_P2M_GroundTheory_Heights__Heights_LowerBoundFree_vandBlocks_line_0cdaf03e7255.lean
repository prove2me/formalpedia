-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_vandBlocks_line_0cdaf03e7255
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T23:38:06.05021+00:00
-- url     : https://prove2.me/submissions/eca94104-3312-47ec-a538-71d8ed3d0242

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv

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
theorem _root_.solution : vandBlocks Unit 2 1 = 1 := by
  unfold vandBlocks
  rw [show (Finset.univ.filter fun ab : Fin 2 × Fin 2 =>
      ab.1 < ab.2 ∧ ((ab.1 : ℕ) < 1 ↔ (ab.2 : ℕ) < 1)) = ∅ by decide]
  simp
end GroundTheory.Heights₂.Heights.LowerBoundFree
