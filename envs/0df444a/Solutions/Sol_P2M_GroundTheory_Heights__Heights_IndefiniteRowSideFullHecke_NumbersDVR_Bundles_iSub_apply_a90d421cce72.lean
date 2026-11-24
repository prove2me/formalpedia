-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_iSub_apply_a90d421cce72
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:55:54.611851+00:00
-- url     : https://prove2.me/submissions/3b70404e-be24-4fae-8c43-c622530586de

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ScaledRankOneLeStandardRankOne

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
set_option linter.unusedSectionVars false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1
variable (O : Type*) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
variable {Ω : Type*} [Field Ω] [Algebra O Ω]
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
theorem _root_.solution (v : Fin 1 → Ω) (j : Fin 2) : iSub v j = if j = 0 then v 0 else 0 :=
  rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
