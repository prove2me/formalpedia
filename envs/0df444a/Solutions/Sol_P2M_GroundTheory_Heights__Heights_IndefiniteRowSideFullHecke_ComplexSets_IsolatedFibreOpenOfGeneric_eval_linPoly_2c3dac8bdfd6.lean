-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_IsolatedFibreOpenOfGeneric_eval_linPoly_2c3dac8bdfd6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:28:00.313637+00:00
-- url     : https://prove2.me/submissions/9b8fdfd8-71cc-474b-85bb-607f229f4d71

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StIsolatedFibreOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteMapOpen
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_IsClosedComplexSubmanifoldIn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PIsolatedFibreOpenFixed

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
open MvPolynomial Filter Topology Matrix Metric
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric
theorem _root_.solution {n k : ℕ} (B : Matrix (Fin k) (Fin n) ℂ) (z : Fin n → ℂ) (i : Fin k) :
    eval z (linPoly B.mulVecLin i) = (B *ᵥ z) i := by
  simp [linPoly, Matrix.mulVec, dotProduct, Pi.single_apply, mul_comm]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.IsolatedFibreOpenOfGeneric
