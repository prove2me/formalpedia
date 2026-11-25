-- Prove2me | solution 1 for P2M_FubiniStudyChowHeightFormula__Adr_qa2_dcbabdd33386
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:59:39.930389+00:00
-- url     : https://prove2.me/submissions/a3ce4aa8-5583-46da-aafb-9293bc109845

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod
import Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_Acyc_zero_4280e36900b5
import Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_Acyc_one_ade2f35a80e2
import Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_Acyc_two_37305c98b3e1
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_class
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
    Function.Bijective (CoefMap.restrict F G).pull2 := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro c hc
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
    obtain ⟨g, hg⟩ := hc
    let f : ∀ S S', (S ⟶ S') → F.obj (G.obj S') := g
    have hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S''), z.1 _ _ _ (G.map φ) (G.map ψ) =
        mp F (G.map ψ) (f S S' φ) - f S S'' (φ ≫ ψ) + f S' S'' ψ := fun S S' S'' φ ψ ↦
      (congrFun (congrFun (congrFun (congrFun (congrFun hg S) S') S'') φ) ψ).symm
    have ex : ∀ T, ∃ v : ∀ S, (G.obj S ⟶ T) → F.obj T, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        z.1 _ _ _ (G.map ψ) c - mp F c (f S S' ψ) = v S' c - v S (G.map ψ ≫ c) := fun T ↦
      (h T).one _ (fun S S' ψ c ↦ z.1 _ _ _ (G.map ψ) c - mp F c (f S S' ψ)) fun S S' S'' φ ψ c ↦ by
        have e := z.2 (G.map φ) (G.map ψ) c
        simp only [hf, mp_comp, map_add, map_sub, Functor.map_comp] at e ⊢
        linear_combination e
    choose v hv using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ m : F.obj T', ∀ S (c : G.obj S ⟶ T),
        z.1 _ _ _ c φ - mp F φ (v T S c) + v T' S (c ≫ φ) = m := fun T T' φ ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e := z.2 (G.map ψ) c φ
        have e1 := hv T' S S' ψ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hv T S S' ψ c)
        simp only [mp_comp, map_sub, Category.assoc] at e1 e2 ⊢
        linear_combination e + e1 - e2
    choose m hm using ex
    refine H2.mk_eq_zero.2 ⟨m, ?_⟩
    funext T T' T'' φ ψ
    obtain ⟨a⟩ := (h T).1
    let c : G.obj a.left ⟶ T := a.hom
    have e := z.2 c φ ψ
    rw [d1_apply, ← hm T T'' _ _ c, ← hm T T' _ _ c, ← hm T' T'' _ _ (c ≫ φ)]
    simp only [mp_comp, map_sub, map_add, Category.assoc]
    linear_combination e
  · intro c
    obtain ⟨z, rfl⟩ := H2.mk_surjective _ c
    let y : ∀ S S' S'', (S ⟶ S') → (S' ⟶ S'') → F.obj (G.obj S'') := z.1
    have hy : ∀ S S' S'' S''' (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S'' ⟶ S'''),
        mp F (G.map χ) (y _ _ _ φ ψ) + y _ _ _ (φ ≫ ψ) χ = y _ _ _ φ (ψ ≫ χ) + y _ _ _ ψ χ :=
      fun S S' S'' S''' φ ψ χ ↦ z.2 φ ψ χ
    have ex : ∀ T, ∃ w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → F.obj T,
        ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
          mp F c (y _ _ _ φ ψ) = w S S' φ (G.map ψ ≫ c) - w S S'' (φ ≫ ψ) c + w S' S'' ψ c := fun T ↦
      (h T).two _ (fun S S' S'' φ ψ c ↦ mp F c (y _ _ _ φ ψ)) fun S S' S'' S''' φ ψ χ c ↦ by
        simp only [mp_comp, ← map_add, hy]
    choose w hw using ex
    have ex : ∀ T T' (φ : T ⟶ T'), ∃ x : ∀ S, (G.obj S ⟶ T) → F.obj T', ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T),
        mp F φ (w T S S' ψ c) - w T' S S' ψ (c ≫ φ) = x S' c - x S (G.map ψ ≫ c) := fun T T' φ ↦
      (h T).one _ (fun S S' ψ c ↦ mp F φ (w T S S' ψ c) - w T' S S' ψ (c ≫ φ)) fun S S' S'' ψ χ c ↦ by
        have e1 := hw T' S S' S'' ψ χ (c ≫ φ)
        have e2 := congrArg (mp F φ) (hw T S S' S'' ψ χ c)
        simp only [mp_comp, map_sub, map_add, Category.assoc] at e1 e2 ⊢
        linear_combination e2 - e1
    choose x hx using ex
    have ex : ∀ T T' T'' (φ : T ⟶ T') (φ' : T' ⟶ T''), ∃ m : F.obj T'', ∀ S (c : G.obj S ⟶ T),
        mp F φ' (x T T' φ S c) + x T' T'' φ' S (c ≫ φ) - x T T'' (φ ≫ φ') S c = m := fun T T' T'' φ φ' ↦
      (h T).zero _ _ fun S S' ψ c ↦ by
        have e1 := congrArg (mp F φ') (hx T T' φ S S' ψ c)
        have e2 := hx T' T'' φ' S S' ψ (c ≫ φ)
        have e3 := hx T T'' (φ ≫ φ') S S' ψ c
        simp only [mp_comp, map_sub, Category.assoc] at e1 e2 e3 ⊢
        linear_combination e1 + e2 - e3
    choose m hm using ex
    refine ⟨H2.mk _ ⟨m, fun T T' T'' T''' φ ψ χ ↦ ?_⟩, ?_⟩
    · obtain ⟨a⟩ := (h T).1
      let c : G.obj a.left ⟶ T := a.hom
      rw [← hm T T' T'' _ _ _ c, ← hm T T'' T''' _ _ _ c, ← hm T T' T''' _ _ _ c, ← hm T' T'' T''' _ _ _ (c ≫ φ)]
      simp only [mp_comp, map_sub, map_add, Category.assoc]; ring
    · rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_mk]
      refine ⟨fun S S' ψ ↦ x _ _ (G.map ψ) S (𝟙 _) - w _ S S' ψ (𝟙 _), ?_⟩
      funext S S' S'' φ ψ
      have e1 := hm _ _ _ (G.map φ) (G.map ψ) S (𝟙 _)
      have e2 := hw _ S S' S'' φ ψ (𝟙 _)
      have e3 := hx _ _ (G.map ψ) S S' φ (𝟙 _)
      rw [Category.id_comp] at e1 e3
      rw [Category.comp_id] at e2 e3
      rw [mp_id] at e2
      change mp F (G.map ψ) (x _ _ (G.map φ) S (𝟙 _) - w _ S S' φ (𝟙 _)) -
        (x _ _ (G.map (φ ≫ ψ)) S (𝟙 _) - w _ S S'' (φ ≫ ψ) (𝟙 _)) + (x _ _ (G.map ψ) S' (𝟙 _) - w _ S' S'' ψ (𝟙 _)) =
        m _ _ _ (G.map φ) (G.map ψ) - y _ _ _ φ ψ
      rw [map_sub, G.map_comp]
      linear_combination e1 + e2 - e3
end FubiniStudyChowHeightFormula₂.Adr
