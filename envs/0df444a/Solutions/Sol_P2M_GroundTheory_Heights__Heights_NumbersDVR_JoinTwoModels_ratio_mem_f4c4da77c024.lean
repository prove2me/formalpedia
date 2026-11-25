-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_JoinTwoModels_ratio_mem_f4c4da77c024
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:33:28.274607+00:00
-- url     : https://prove2.me/submissions/7d36ab06-88e5-44aa-b046-28ebc3a0e480

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ImportsTerSide
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_ClassListMapDomainPerm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PGenericProjClosureDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PDvrConeDimTrdeg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PTwinJoinTwoModels

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcIdeal joinCoord fnField)
open GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels
variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels
theorem _root_.solution {K' : Type} {ι' : K' → Type} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω)
    (h : fnField O (joinCoord x z) = fnField O x) (k : K') (i j : ι' k) :
    z ⟨k, i⟩ / z ⟨k, j⟩ ∈ fnField O x := by
  rw [← h]
  exact Subfield.subset_closure (Or.inr ⟨⟨.inr k, (i, j)⟩, rfl⟩)
end GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels
