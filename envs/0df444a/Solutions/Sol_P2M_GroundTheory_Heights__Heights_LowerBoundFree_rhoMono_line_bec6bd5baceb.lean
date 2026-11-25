-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_rhoMono_line_bec6bd5baceb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:29.857499+00:00
-- url     : https://prove2.me/submissions/f578dd1f-6a2c-43c6-a247-5c038fb7b75d

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
theorem _root_.solution : rhoMono Unit 2 = Finsupp.single ((), 0) 1 := by
  ext ⟨u, i⟩
  fin_cases i <;> simp [rhoMono, Finsupp.single_apply]
end GroundTheory.Heights₂.Heights.LowerBoundFree
