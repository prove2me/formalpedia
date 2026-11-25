-- Prove2me | solution 1 for P2M_GlobalTheory_Kempf_map_toInter___eq_zero_4ac7f8313bcd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:31:37.264241+00:00
-- url     : https://prove2.me/submissions/f67e9464-5f62-4eeb-8ec1-d6a263ce004e

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_CohomologyPresheafFunctorMapAppApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_IsIsoToInterAppPushforwardInclusion
import Theorems.Thm_GlobalTheory_Kempf_exact_map_interSheaf
import Theorems.Thm_GlobalTheory_SheafLES_map_comp
import Theorems.Thm_GlobalTheory_SheafLES_map_equivZero_symm
import Theorems.Thm_GlobalTheory_SheafLES_map_zero_injective_of_mono
import Theorems.Thm_P2M_GlobalTheory_SheafLES___naturality_d0a1c18f99f7
import Theorems.Thm_P2M_GlobalTheory_SheafLES_exact__24269ba80ece


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits Opposite TopologicalSpace
universe w u v' u'
noncomputable section
open GlobalTheory
open GlobalTheory.Kempf
variable {X : TopCat.{u}}
variable {S : ShortComplex (X.Sheaf AddCommGrpCat.{u})}
variable [HasExt.{w} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
open SheafLES
namespace GlobalTheory.Kempf
theorem _root_.solution (hS : S.ShortExact) {V W : Opens X} (s : S.X₃.obj.obj (op V))
    (t : S.X₂.obj.obj (op (V ⊓ W)))
    (ht : S.g.hom.app (op (V ⊓ W)) t = S.X₃.obj.map (homOfLE inf_le_left).op s) :
    map.{w} ((toInter AddCommGrpCat.{u} W).app S.X₁) 1 V
      (δ hS 0 V ((equivZero S.X₃ V).symm s)) = 0 := by
  have := hS.epi_g
  let S' := S.map (interSheaf AddCommGrpCat.{u} W)
  have hS' : S'.Exact := (exact_map_interSheaf hS W).1
  have : Mono S'.f := (exact_map_interSheaf hS W).2
  let T : ShortComplex (X.Sheaf AddCommGrpCat.{u}) :=
    ShortComplex.mk S'.f (cokernel.π S'.f) (cokernel.condition _)
  have hT : T.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel _) }
  let ι : T.X₃ ⟶ S'.X₃ := cokernel.desc S'.f S'.g S'.zero
  have hm : Mono ι := S'.exact_iff_mono_cokernel_desc.1 hS'
  have hι : T.g ≫ ι = S'.g := cokernel.π_desc _ _ _
  let η₁ : S.X₁ ⟶ T.X₁ := (toInter AddCommGrpCat.{u} W).app S.X₁
  let η₂ : S.X₂ ⟶ T.X₂ := (toInter AddCommGrpCat.{u} W).app S.X₂
  let η₃ : S.X₃ ⟶ S'.X₃ := (toInter AddCommGrpCat.{u} W).app S.X₃
  have h₁₂ : S.f ≫ η₂ = η₁ ≫ T.f := (toInter AddCommGrpCat.{u} W).naturality S.f
  have h₂₃ : S.g ≫ η₃ = η₂ ≫ S'.g := (toInter AddCommGrpCat.{u} W).naturality S.g
  have h0 : S.f ≫ η₂ ≫ T.g = 0 := by rw [reassoc_of% h₁₂, T.zero, comp_zero]
  let φ : S ⟶ T := ⟨η₁, η₂, hS.exact.desc (η₂ ≫ T.g) h0, h₁₂.symm, (hS.exact.g_desc _ h0).symm⟩
  have hφ : φ.τ₃ ≫ ι = η₃ := by
    rw [← cancel_epi S.g, ← φ.comm₂₃_assoc, hι, h₂₃]
  refine (δ_naturality hS hT φ 0 V _).trans ?_
  refine (exact₃ hT 0 V _).2 ⟨(equivZero T.X₂ V).symm t,
    @map_zero_injective_of_mono _ _ _ _ _ _ _ ι hm V _ _ ?_⟩
  refine (map_comp T.g ι 0 V _).symm.trans (Eq.trans ?_ (map_comp φ.τ₃ ι 0 V _))
  refine (congrArg (fun g ↦ map.{w} g 0 V ((equivZero T.X₂ V).symm t)) hι).trans
    (Eq.trans ?_ (congrArg (fun g ↦ map.{w} g 0 V ((equivZero S.X₃ V).symm s)) hφ).symm)
  refine (map_equivZero_symm S'.g V t).trans (Eq.trans ?_ (map_equivZero_symm η₃ V s).symm)
  exact congrArg _ ht
end GlobalTheory.Kempf
