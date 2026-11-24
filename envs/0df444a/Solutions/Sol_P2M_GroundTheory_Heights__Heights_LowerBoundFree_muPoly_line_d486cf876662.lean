-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_muPoly_line_d486cf876662
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:26.459802+00:00
-- url     : https://prove2.me/submissions/e258bb02-b880-41c5-8a74-05a6aae968ac

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
theorem _root_.solution : muPoly Unit 2 1 = X ((), 1) := by
  unfold muPoly
  rw [show (Finset.univ.filter fun p : Unit × Fin 2 => ¬ (p.2 : ℕ) < 1) = {((), 1)} by decide]
  simp
end GroundTheory.Heights₂.Heights.LowerBoundFree
