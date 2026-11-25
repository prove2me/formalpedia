-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_basis_det_comp_6ef76de755bd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:31:20.889002+00:00
-- url     : https://prove2.me/submissions/3930ef39-b714-4169-84b1-caa076ffdc42

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
theorem _root_.solution (q : Fin 2 → Fin 2) :
    (Pi.basisFun Ω (Fin 2)).det (Pi.basisFun Ω (Fin 2) ∘ q) = (detInt q : Ω) := by
  rw [Module.Basis.det_apply, detInt, Int.cast_det]
  congr 1
  ext p a
  simp [Module.Basis.toMatrix_apply, Pi.single_apply, eq_comm]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
