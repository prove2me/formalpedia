-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_fdeg_line_a7beef4d3cda
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:04:53.751804+00:00
-- url     : https://prove2.me/submissions/228394c5-54f9-443b-9bec-e10ddf1b7ffc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_PermFinTwoUniv
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
theorem _root_.solution : fdeg Unit 2 1 = 1 := by
  unfold fdeg blockInt
  rw [vandBlocks_line]
  rw [show (Finset.univ.filter (IsBlockPerm Unit 2 1)) = {fun _ => 1} by decide]
  have : rhoBlock Unit 2 1 = 0 := by
    ext ⟨u, i⟩
    fin_cases i <;> simp [rhoBlock]
  simp [this, weylSign]
end GroundTheory.Heights₂.Heights.LowerBoundFree
