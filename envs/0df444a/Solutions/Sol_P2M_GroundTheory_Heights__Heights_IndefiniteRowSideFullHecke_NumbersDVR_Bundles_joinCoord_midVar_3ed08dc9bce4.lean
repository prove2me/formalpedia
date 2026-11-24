-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_NumbersDVR_Bundles_joinCoord_midVar_3ed08dc9bce4
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:44:52.69341+00:00
-- url     : https://prove2.me/submissions/4dda7cc0-7efe-4ca2-83c2-88d080feca33

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_InstFintypeSumElim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_JoinCoordMidVar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
variable {K K' K₂ : Type} {ι : K → Type} {ι' : K' → Type}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
theorem _root_.solution {Ω : Type*} (x : (Σ k, ι k) → Ω) (z : (Σ k, ι' k) → Ω) {ι₂ : K₂ → Type}
    (w : (Σ k, ι₂ k) → Ω) (p : Σ k : K ⊕ K', Sum.elim ι ι' k) :
    joinCoord x (joinCoord w z) (midVar ι₂ p) = joinCoord x z p := by
  obtain ⟨k | k, i⟩ := p <;> rfl
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.NumbersDVR.Bundles
