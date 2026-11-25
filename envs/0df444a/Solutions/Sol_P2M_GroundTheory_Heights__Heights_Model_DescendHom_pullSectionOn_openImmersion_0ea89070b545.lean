-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DescendHom_pullSectionOn_openImmersion_0ea89070b545
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:26:03.175507+00:00
-- url     : https://prove2.me/submissions/af8d5f76-0a1d-4a95-bcc8-c66a589c3195

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsDescendHom
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PClearDenominators
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDescendHom

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
open GroundTheory.Heights₂.Heights.Model.DescendHom
variable {T Y Z : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model.DescendHom
theorem _root_.solution (ι : Z ⟶ Y) [IsOpenImmersion ι] (M : Y.Modules) (O : Y.Opens)
    (m : Γ(M, O)) :
    pullSectionOn ι M O m = ((Scheme.Modules.restrictFunctorIsoPullback ι).hom.app M).app (ι ⁻¹ᵁ O)
      ((M.restrictAppIso ι (ι ⁻¹ᵁ O)).inv (M.presheaf.map (homOfLE (ι.image_preimage_le O)).op m)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app (Scheme.Modules.restrictAdjunction ι)
    (Scheme.Modules.pullbackPushforwardAdjunction ι) M
  rw [pullSectionOn, ← h]
  rfl
end GroundTheory.Heights₂.Heights.Model.DescendHom
