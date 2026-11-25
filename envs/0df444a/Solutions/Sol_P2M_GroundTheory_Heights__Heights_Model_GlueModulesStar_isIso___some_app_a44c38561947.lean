-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_app_a44c38561947
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:40:39.238393+00:00
-- url     : https://prove2.me/submissions/cb0bb7d2-71be-4418-bd85-9fd53b6942ad

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_StatementsGlue
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PGlueModulesStar
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso___some_f8685ded3020
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_GlueModulesStar_isIso_transMap_app_9788faf886f2

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
open GroundTheory.Heights₂.Heights.Model.GlueModulesStar
universe u
variable {X : Scheme.{u}} (V : X.Opens) {ι : Type u} (U : ι → X.Opens)
  (G : (V : Scheme.{u}).Modules) (F : ∀ i, (U i : Scheme.{u}).Modules)
  (ψ : ∀ i, (Scheme.Modules.pullback (X.homOfLE (inf_le_left : U i ⊓ V ≤ U i))).obj (F i) ≅
    (Scheme.Modules.pullback (X.homOfLE (inf_le_right : U i ⊓ V ≤ V))).obj G)
set_option backward.isDefEq.respectTransparency false
namespace GroundTheory.Heights₂.Heights.Model.GlueModulesStar
theorem _root_.solution (hUU : ∀ i j, i ≠ j → U i ⊓ U j ≤ V) (i : ι) (W : X.Opens)
    (hW : W ≤ U i) : IsIso ((Multiequalizer.ι (index V U G F ψ) (some i)).app W) := by
  classical
  let Fw : X.Modules ⥤ AddCommGrpCat.{u} := Scheme.Modules.toPresheaf X ⋙ (evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W)
  have : PreservesLimitsOfShape (WalkingMulticospan (starShape ι))
      ((evaluation (X.Opens)ᵒᵖ AddCommGrpCat.{u}).obj (op W)) :=
    evaluation_preservesLimitsOfShape _
  have : PreservesLimitsOfShape (WalkingMulticospan (starShape ι)) Fw :=
    comp_preservesLimitsOfShape _ _
  have hK := Multifork.isLimitMapOfPreserves (Multiequalizer.multifork (index V U G F ψ)) Fw
    (limit.isLimit (index V U G F ψ).multicospan)
  refine isIso_ι_some hK i (isIso_transMap_app _ _ _ _ W ?_)
    (fun j hj => isIso_transMap_app _ _ _ _ W ?_)
  · rw [Scheme.opensRange_homOfLE]
    intro x hx
    exact ⟨hW hx, by simp⟩
  · rw [Scheme.opensRange_homOfLE]
    intro x hx
    exact ⟨by simp, hUU i j (Ne.symm hj) ⟨hW hx, by simp⟩⟩
end GroundTheory.Heights₂.Heights.Model.GlueModulesStar
