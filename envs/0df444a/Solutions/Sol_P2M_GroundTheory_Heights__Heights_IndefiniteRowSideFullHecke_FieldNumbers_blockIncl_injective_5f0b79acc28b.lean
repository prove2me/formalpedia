-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_FieldNumbers_blockIncl_injective_5f0b79acc28b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:59:36.871514+00:00
-- url     : https://prove2.me/submissions/4efe8f73-3f9b-4bd3-b608-9fe8714a3e43

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PfContractedHypothesesExample

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u u' v v' w
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
theorem _root_.solution {F : Type u} [Field F] {K : Type v} {L : Type v'} {ι : K → Type w}
    (ι₂ : L → Type w) : Function.Injective (blockIncl (F := F) (ι := ι) ι₂) := by
  exact rename_injective _ (Function.Injective.sigma_map (β₂ := Sum.elim ι ι₂)
    (f₁ := Sum.inl) (f₂ := fun _ x => x) Sum.inl_injective fun _ _ _ h => h)
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.FieldNumbers
