-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_uMat_diag_9ca96a409312
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:29:02.539583+00:00
-- url     : https://prove2.me/submissions/408c5ee5-71e8-4894-b525-44e2fd3b9197

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution (F : Type) [Field F] {n : ℕ} (r : ℕ) (hr : r + 1 < n) :
    uMat F n ⟨r, by omega⟩ ⟨r, by omega⟩ = X (Sum.inr ⟨r, by omega⟩) := by
  simp [uMat, hr]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
