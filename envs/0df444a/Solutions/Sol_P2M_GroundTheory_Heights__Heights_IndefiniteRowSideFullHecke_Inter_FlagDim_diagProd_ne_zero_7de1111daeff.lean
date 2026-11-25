-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_ne_zero_7de1111daeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:39:38.682911+00:00
-- url     : https://prove2.me/submissions/c2f5b2cd-72e5-4018-ae43-4c746492584c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_FlagDimSt
import Definitions.Def_GroundTheory_ArithmeticGeometry_AbelianVarieties_JacobianSmoothness_RingKrullDimLeRingKrullDimQuotientAddOne
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PFlagDim
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_uMat_diag_9ca96a409312

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
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution (r : ℕ) (hr : r < n) : diagProd F n r hr ≠ 0 := by
  rw [diagProd, Finset.prod_ne_zero_iff]
  intro k _
  rw [uMat_diag F k.val (by omega)]
  exact X_ne_zero _
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
