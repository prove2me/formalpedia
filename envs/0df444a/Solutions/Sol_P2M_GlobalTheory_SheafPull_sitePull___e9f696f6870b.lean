-- Prove2me | solution 1 for P2M_GlobalTheory_SheafPull_sitePull___e9f696f6870b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T21:01:34.918222+00:00
-- url     : https://prove2.me/submissions/9b8d1201-7c18-4c7c-986d-56bc5c94091d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_FreeYonedaHomEquivFreeToPullbackComp
import Theorems.Thm_GlobalTheory_SheafPull_extMap_extClass
import Theorems.Thm_P2M_GlobalTheory_SheafLES___apply_7b49c5df3cf6


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
variable {C D : Type u} [Category.{v} C] [Category.{v} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  [HasSheafify J AddCommGrpCat.{v}] [HasSheafify K AddCommGrpCat.{v}]
  (p : C ⥤ D) [p.IsContinuous J K]
  [(p.sheafPushforwardContinuous AddCommGrpCat.{v} J K).IsRightAdjoint]
open SheafLES
variable [PreservesFiniteLimits (p.sheafPullback AddCommGrpCat.{v} J K)]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{v})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{v})]
  {F F' : Sheaf J AddCommGrpCat.{v}} {G G' : Sheaf K AddCommGrpCat.{v}}
namespace GlobalTheory.SheafPull
theorem _root_.solution {S : ShortComplex (Sheaf J AddCommGrpCat.{v})}
    {T : ShortComplex (Sheaf K AddCommGrpCat.{v})} (hS : S.ShortExact) (hT : T.ShortExact)
    (φ : S ⟶ T.map (p.sheafPushforwardContinuous AddCommGrpCat.{v} J K)) (n : ℕ)
    {V : C} {W : D} (i : W ⟶ p.obj V) (x : Sheaf.H'.{w} S.X₃ n V) :
    sitePull.{w, w'} p (G := T.X₁) φ.τ₁ (n + 1) i (δ hS n V x) =
      δ hT n W (sitePull.{w, w'} p (G := T.X₃) φ.τ₃ n i x) := by
  have h1 := extMap_extClass (p.sheafPullback AddCommGrpCat.{v} J K) (freeToPullback J K p i) hS hT
    { τ₁ := ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ.τ₁
      τ₂ := ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ.τ₂
      τ₃ := ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm φ.τ₃
      comm₁₂ := by
        have h := congrArg ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm
          φ.comm₁₂
        exact (Adjunction.homEquiv_naturality_right_symm _ _ _).symm.trans
          (h.trans (Adjunction.homEquiv_naturality_left_symm _ _ _))
      comm₂₃ := by
        have h := congrArg ((p.sheafAdjunctionContinuous AddCommGrpCat.{v} J K).homEquiv _ _).symm
          φ.comm₂₃
        exact (Adjunction.homEquiv_naturality_right_symm _ _ _).symm.trans
          (h.trans (Adjunction.homEquiv_naturality_left_symm _ _ _)) } n x
  exact (congrArg (fun y => sitePull.{w, w'} p (G := T.X₁) φ.τ₁ (n + 1) i y) (δ_apply hS n V x)).trans
    (h1.trans (δ_apply hT n W _).symm)
end GlobalTheory.SheafPull
