-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_Objects_linPoly_eq_6d48c9ef34e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:15.263694+00:00
-- url     : https://prove2.me/submissions/62d93078-77a3-45ba-8951-748d88fbe2be

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_ProjDegreeEqFinrankAdjoin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.Objects
variable {n d : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.Objects
theorem _root_.solution (A : Matrix (Fin d) (Fin n) ℂ) (i : Fin d) :
    linPoly A.mulVecLin i = GroundTheory.Heights₂.Heights.ComplexSets.linPoly A i := by
  simp [linPoly, GroundTheory.Heights₂.Heights.ComplexSets.linPoly]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.Objects
