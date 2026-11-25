-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_spreadNbhd_of_isEmpty_9b72b381a6b7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:27:23.966015+00:00
-- url     : https://prove2.me/submissions/824411b2-94be-413d-bfea-5fbd3c85ee05

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadNbhd
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsSpreadStep
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PSpreadBundleNbhd

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
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Opposite
noncomputable section
variable {X : Scheme.{0}}
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (f : X ⟶ SpecZ) (R : Type) [CommRing R] [IsEmpty (baseChange f R)]
    (E : (baseChange f R).Modules) :
    ∃ (W : X.Opens) (hW : Set.range (baseChangeMap f R) ⊆ Set.range W.ι)
      (E' : (W : Scheme.{0}).Modules), IsVectorBundle E' ∧
        Nonempty ((Scheme.Modules.pullback (toOpen f R W hW)).obj E' ≅ E) := by
  have hW : Set.range (baseChangeMap f R) ⊆ Set.range (⊥ : X.Opens).ι := by
    rintro _ ⟨y, rfl⟩
    exact isEmptyElim y
  have : IsEmpty ((⊥ : X.Opens) : Scheme.{0}) := ⟨fun x => x.2⟩
  let i : ((⊥ : X.Opens) : Scheme.{0}) ⟶ baseChange f R := isInitialOfIsEmpty.to _
  have hi : toOpen f R ⊥ hW ≫ i = 𝟙 _ := isInitialOfIsEmpty.hom_ext _ _
  exact ⟨⊥, hW, (Scheme.Modules.pullback i).obj E, fun x => isEmptyElim x,
    ⟨(Scheme.Modules.pullbackComp _ i).app E ≪≫ (Scheme.Modules.pullbackCongr hi).app E ≪≫
      (Scheme.Modules.pullbackId _).app E⟩⟩
end GroundTheory.Heights₂.Heights.Model
