-- Prove2me | solution 1 for P2M_FubiniStudyChowHeightFormula__Adr_Acyc_two_37305c98b3e1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:48:58.745882+00:00
-- url     : https://prove2.me/submissions/955cefab-cbc9-43fd-8b84-6c1b6ee888c9

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
    (z : ∀ S S' S'', (S ⟶ S') → (S' ⟶ S'') → (G.obj S'' ⟶ T) → M)
    (hz : ∀ S S' S'' S''' (φ : S ⟶ S') (ψ : S' ⟶ S'') (χ : S'' ⟶ S''') (c : G.obj S''' ⟶ T),
      z S S' S'' φ ψ (G.map χ ≫ c) + z S S'' S''' (φ ≫ ψ) χ c = z S S' S''' φ (ψ ≫ χ) c + z S' S'' S''' ψ χ c) :
    ∃ w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M, ∀ S S' S'' (φ : S ⟶ S') (ψ : S' ⟶ S'') (c : G.obj S'' ⟶ T),
      z S S' S'' φ ψ c = w S S' φ (G.map ψ ≫ c) - w S S'' (φ ≫ ψ) c + w S' S'' ψ c := by
  let z' : Z2 ((Functor.const (CostructuredArrow G T)).obj M) :=
    ⟨fun a b c φ ψ ↦ (z a.left b.left c.left φ.left ψ.left c.hom : M), fun a b c e φ ψ χ ↦
      (congrArg (fun t ↦ z _ _ _ φ.left ψ.left t + z _ _ _ (φ.left ≫ ψ.left) χ.left e.hom)
        (CostructuredArrow.w χ)).symm.trans (hz _ _ _ _ φ.left ψ.left χ.left e.hom)⟩
  obtain ⟨g, hg⟩ := H2.mk_eq_zero.1 ((h.2 M).2.2 (H2.mk _ z'))
  let w : ∀ S S', (S ⟶ S') → (G.obj S' ⟶ T) → M := fun S S' ψ c ↦
    g (CostructuredArrow.mk (G.map ψ ≫ c)) (CostructuredArrow.mk c) (CostructuredArrow.homMk ψ rfl)
  have hw : ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T) (c₀ : G.obj S ⟶ T) (e : G.map ψ ≫ c = c₀),
      (g (CostructuredArrow.mk c₀) (CostructuredArrow.mk c) (CostructuredArrow.homMk ψ e) : M) = w S S' ψ c := by
    intro S S' ψ c c₀ e
    subst e
    rfl
  refine ⟨w, fun S S' S'' φ ψ c ↦ ?_⟩
  have k := congrFun (congrFun (congrFun (congrFun (congrFun hg
    (CostructuredArrow.mk (G.map φ ≫ G.map ψ ≫ c))) (CostructuredArrow.mk (G.map ψ ≫ c))) (CostructuredArrow.mk c))
      (CostructuredArrow.homMk φ rfl)) (CostructuredArrow.homMk ψ rfl)
  rw [← hw S S'' (φ ≫ ψ) c (G.map φ ≫ G.map ψ ≫ c) (by simp)]
  exact k.symm
end Acyc
end FubiniStudyChowHeightFormula₂.Adr
