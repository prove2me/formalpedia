-- Prove2me | solution 1 for P2M_FubiniStudyChowHeightFormula__Adr_qa1_7c8b1fea16fe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:49:02.287966+00:00
-- url     : https://prove2.me/submissions/c57d8e03-7c55-4033-b55f-04516ca0e641

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod
import Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_Acyc_zero_4280e36900b5
import Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_Acyc_one_ade2f35a80e2
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_class
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H1_mk_surjective
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_eq_mk
import Theorems.Thm_GlobalTheory_CatCoh_H2_mk_surjective


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory GlobalTheory.CatCoh
open FubiniStudyChowHeightFormula₂ FubiniStudyChowHeightFormula₂.Adr
universe v u v' u'
variable {R : Type} [CommRing R] {C : Type u} [Category.{v} C] {C' : Type u'} [Category.{v'} C']
namespace FubiniStudyChowHeightFormula₂.Adr
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (h : ∀ T, Acyc R (CostructuredArrow G T)) :
    Function.Bijective (CoefMap.restrict F G).pull1 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let g' : ∀ S, F.obj (G.obj S) := g
    have hg' : ∀ S S' (ψ : S ⟶ S'), f.1 _ _ (G.map ψ) = g' S' - mp F (G.map ψ) (g' S) := fun S S' ψ ↦
      (congrFun (congrFun (congrFun hg S) S') ψ).symm
    have ex : ∀ T, ∃ m : F.obj T, ∀ S (c : G.obj S ⟶ T), f.1 _ _ c + mp F c (g' S) = m := fun T ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        simp only [Z1.comp f, hg', mp_comp, map_sub]; ring
    choose m hm using ex
    refine H1.mk_eq_zero.2 ⟨m, ?_⟩
    funext T T' φ
    obtain ⟨a⟩ := (h T).1
    let c : G.obj a.left ⟶ T := a.hom
    rw [amitsur_d0_apply, ← hm T _ c, ← hm T' _ (c ≫ φ)]
    simp only [Z1.comp f, mp_comp, map_add]; ring
  · intro c
    obtain ⟨f, rfl⟩ := H1.mk_surjective _ c
    let f' : ∀ S S', (S ⟶ S') → F.obj (G.obj S') := f.1
    have hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S''),
        f' S S'' (φ ≫ ψ) = mp F (G.map ψ) (f' S S' φ) + f' S' S'' ψ := fun S S' S'' φ ψ ↦ f.2 φ ψ
    have ex : ∀ T, ∃ v : ∀ S, (G.obj S ⟶ T) → F.obj T, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        -mp F c (f' S S' ψ) = v S' c - v S (G.map ψ ≫ c) := fun T ↦
      (h T).one _ (fun S S' ψ c ↦ -mp F c (f' S S' ψ)) fun S S' S'' φ ψ c ↦ by
        simp only [hf, mp_comp, map_add]; ring
    choose v hv using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ m : F.obj T', ∀ S (c : G.obj S ⟶ T),
        v T' S (c ≫ φ) - mp F φ (v T S c) = m := fun T T' φ ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e1 := hv T' S S' ψ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hv T S S' ψ c)
        simp only [mp_comp, map_sub, map_neg, Category.assoc] at e1 e2 ⊢
        linear_combination e1 - e2
    choose m hm using ex
    refine ⟨H1.mk _ ⟨m, fun T T' T'' φ ψ ↦ ?_⟩, ?_⟩
    · obtain ⟨a⟩ := (h T).1
      let c : G.obj a.left ⟶ T := a.hom
      rw [← hm T T'' _ _ c, ← hm T T' _ _ c, ← hm T' T'' _ _ (c ≫ φ)]
      simp only [mp_comp, map_sub, Category.assoc]; ring
    · rw [CoefMap.pullCohomologyOne_class, H1.mk_eq_mk]
      refine ⟨fun S ↦ v _ S (𝟙 _), ?_⟩
      funext S S' ψ
      have e1 := hm _ _ (G.map ψ) S (𝟙 _)
      have e2 := hv _ S S' ψ (𝟙 _)
      rw [Category.id_comp] at e1
      rw [Category.comp_id, mp_id] at e2
      change v _ S' (𝟙 _) - mp F (G.map ψ) (v _ S (𝟙 _)) = m _ _ (G.map ψ) - f' S S' ψ
      linear_combination e1 - e2
end FubiniStudyChowHeightFormula₂.Adr
