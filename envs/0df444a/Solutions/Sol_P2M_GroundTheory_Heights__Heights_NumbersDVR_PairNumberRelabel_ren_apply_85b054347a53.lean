-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PairNumberRelabel_ren_apply_85b054347a53
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T07:16:25.476632+00:00
-- url     : https://prove2.me/submissions/2b7c7993-ea7e-4504-9f4f-19ad136fa1cc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPairNumberRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_IntNumRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PRenameMultiProjPrime
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_PExistsUniqueRelabel
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPairNumberRelabel

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
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
variable {K₁ K₂ : Type} {ι₁ : K₁ → Type} {ι₂ : K₂ → Type} {R : Type} [CommRing R]
  (σ : (Σ k, ι₁ k) ≃ (Σ k, ι₂ k))
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
theorem _root_.solution (f : MRing ι₁ R) : ren (R := R) σ f = rename σ f := rfl
end GroundTheory.Heights₂.Heights.NumbersDVR.PairNumberRelabel
