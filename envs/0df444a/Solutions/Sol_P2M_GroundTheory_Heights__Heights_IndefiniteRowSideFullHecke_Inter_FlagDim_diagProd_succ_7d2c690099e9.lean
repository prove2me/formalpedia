-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_FlagDim_diagProd_succ_7d2c690099e9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T02:28:44.398814+00:00
-- url     : https://prove2.me/submissions/119211a8-5580-4f57-a8a8-b99dbd57ed26

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
variable (F : Type) [Field F] (n : ℕ)
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
theorem _root_.solution (i : ℕ) (h : i + 1 < n) :
    diagProd F n (i + 1) h = diagProd F n i (by omega) * uMat F n ⟨i, by omega⟩ ⟨i, by omega⟩ := by
  rw [diagProd, Fin.prod_univ_castSucc]
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.FlagDim
