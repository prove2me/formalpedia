-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_semiToLoc_coe_6afe5d0b143c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:47.275803+00:00
-- url     : https://prove2.me/submissions/1a84e01c-49a8-46e5-8e90-04b821236742

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsFibreIncomp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_OneNotMemOfIsPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsSemilocMaxIdeals

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (P : Ideal (MRing ι)) (𝒲 : Set (Ideal (MRing ι))) (W : Ideal (MRing ι)) (hW : W ∈ 𝒲)
    (b : semiLocRing P 𝒲) : ((semiToLoc P 𝒲 W hW b : locRing P W) : FractionRing (MRing ι ⧸ P)) = b := by
  simp [semiToLoc]
end GroundTheory.Heights₂.Heights.Inter
