-- Prove2me | solution 1 for P2M_GlobalTheory_SheafPull_extMap_mk__8ca0febd9656
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T02:31:50.078449+00:00
-- url     : https://prove2.me/submissions/4d0b76ce-23c0-4d18-9168-19f3ede270e7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafPull_extMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Abelian Opposite Limits TopologicalSpace
universe w w' w'' v u u₁ v₁ u₂ v₂
noncomputable section
open GlobalTheory
open GlobalTheory.SheafPull
variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasExt.{w} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasExt.{w'} B]
  (Φ : A ⥤ B) [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]
namespace GlobalTheory.SheafPull
theorem _root_.solution {Z F : A} {Z' G : B} (a : Z' ⟶ Φ.obj Z) (b : Φ.obj F ⟶ G) (g : Z ⟶ F) :
    extMap.{w, w'} Φ a b 0 (Ext.mk₀ g) = Ext.mk₀ (a ≫ Φ.map g ≫ b) := by
  rw [extMap_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀]
end GlobalTheory.SheafPull
