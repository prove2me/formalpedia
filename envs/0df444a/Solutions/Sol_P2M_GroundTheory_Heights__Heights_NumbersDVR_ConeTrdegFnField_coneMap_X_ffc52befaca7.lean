-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_ConeTrdegFnField_coneMap_X_ffc52befaca7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:06:03.666839+00:00
-- url     : https://prove2.me/submissions/6f9c71ac-4124-4dac-a013-e2280d260060

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsConeTrdegFnField
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PConeTrdegFnField

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRingOver)
open IndefiniteRowSideFullHecke.NumbersDVR.Bundles (mcMap mcIdeal fnField)
noncomputable section
variable {O : Type} [CommRing O] {Ω : Type} [Field Ω] [Algebra O Ω]
variable {K : Type} {ι : K → Type}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace ConeTrdegFnField
theorem _root_.solution (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (k : K) :
    ConeTrdegFnField.coneMap (O := O) y c (X k) = C (y ⟨k, c k⟩) * X k := by
  simp [ConeTrdegFnField.coneMap]
end ConeTrdegFnField
end GroundTheory.Heights₂.Heights.NumbersDVR
