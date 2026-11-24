-- Prove2me | solution 1 for P2M_FubiniStudyChowHeightFormula__Adr_Acyc_zero_4280e36900b5
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:50:15.660947+00:00
-- url     : https://prove2.me/submissions/4b899f5c-b0f5-4049-860d-e64f5354f244

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
theorem _root_.solution (h : Acyc R (CostructuredArrow G T)) (M : CommAlgCat.{0} R) (g : ∀ S, (G.obj S ⟶ T) → M)
    (hg : ∀ S S' (ψ : S ⟶ S') (c : G.obj S' ⟶ T), g S (G.map ψ ≫ c) = g S' c) : ∃ m, ∀ S c, g S c = m := by
  obtain ⟨⟨a⟩, h⟩ := h
  refine ⟨g a.left a.hom, fun S c ↦ (h M).1 (fun b ↦ g b.left b.hom) (fun b b' φ ↦ ?_) (CostructuredArrow.mk c) a⟩
  exact (hg _ _ φ.left b'.hom).symm.trans (congrArg _ (CostructuredArrow.w φ))
end Acyc
end FubiniStudyChowHeightFormula₂.Adr
