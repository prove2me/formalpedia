-- Prove2me | solution 1 for P2M_FubiniStudyChowHeightFormula__Adr_Acyc_one_ade2f35a80e2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:43.987176+00:00
-- url     : https://prove2.me/submissions/e58d0e12-0726-4911-b578-d976734baab3

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod

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
  {G : C' ⥤ C} {T : C}
namespace FubiniStudyChowHeightFormula₂.Adr
namespace Acyc
theorem _root_.solution (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R)
    (f : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M)
    (hf : ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      f S S'' (φ ≫ ψ) c = f S S' φ (G.map ψ ≫ c) + f S' S'' ψ c) :
    ∃ v : ∀ S, (G.obj S ⟶ T) → M, ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), f S S' ψ c = v S' c - v S (G.map ψ ≫ c) := by
  let f' : Z1 ((Functor.const (CostructuredArrow G T)).obj M) :=
    ⟨fun a b φ ↦ (f a.left b.left φ.left b.hom : M), fun a b c φ ψ ↦
      (hf _ _ _ φ.left ψ.left c.hom).trans
        (congrArg (fun t ↦ f _ _ φ.left t + f _ _ ψ.left c.hom) (CostructuredArrow.w ψ))⟩
  obtain ⟨g, hg⟩ := H1.mk_eq_zero.1 ((h.2 M).2.1 (H1.mk _ f'))
  exact ⟨fun S c ↦ g (CostructuredArrow.mk c), fun S S' ψ c ↦
    (congrFun (congrFun (congrFun hg (CostructuredArrow.mk (G.map ψ ≫ c))) (CostructuredArrow.mk c))
      (CostructuredArrow.homMk ψ rfl)).symm⟩
end Acyc
end FubiniStudyChowHeightFormula₂.Adr
