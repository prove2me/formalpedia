-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LocalGraphMass_frameProj_basisFun_repr_3fd2d1412cc3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T04:02:57.884687+00:00
-- url     : https://prove2.me/submissions/374eb3d9-86bf-48bc-9dd8-f148aec5bce4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StLocalGraphMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PLocalGraphMass

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
open MeasureTheory Function
open scoped ENNReal
noncomputable section
open GroundTheory.Heights₂.Heights.LocalGraphMass
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.LocalGraphMass
theorem _root_.solution (b : OrthonormalBasis (Fin n) ℂ (EuclideanSpace ℂ (Fin n)))
    (I : Finset (Fin n)) (z : EuclideanSpace ℂ (Fin n)) :
    frameProj (EuclideanSpace.basisFun (Fin n) ℂ) I (b.repr z) = frameProj b I z := by
  funext i
  simp only [frameProj]
  rw [EuclideanSpace.basisFun_inner, b.repr_apply_apply]
end GroundTheory.Heights₂.Heights.LocalGraphMass
