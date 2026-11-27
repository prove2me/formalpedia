-- Prove2me | solution 1 for P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_coprod_19beab630525
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T04:50:41.823584+00:00
-- url     : https://prove2.me/submissions/9dc87153-b5b2-4a39-84e7-e06e912c4cd1

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod
import Theorems.Thm_P2M_FubiniStudyChowHeightFormula__Adr_acyc_of_zigzag_13f90d6b760d

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
variable {R : Type} [CommRing R] {D : Type u} [Category.{v} D]
namespace FubiniStudyChowHeightFormula₂.Adr
theorem _root_.solution (d : D) (P : D → D) (i : ∀ a, a ⟶ P a) (j : ∀ a, d ⟶ P a)
    (h : ∀ a b (φ : a ⟶ P b), ∃! ψ : P a ⟶ P b, i a ≫ ψ = φ ∧ j a ≫ ψ = j b) : Acyc R D := by
  choose m hm hu using h
  let Q : D ⥤ D :=
    { obj := P
      map := fun {a b} φ ↦ m a b (φ ≫ i b)
      map_id := fun a ↦ (hu a a _ (𝟙 _) ⟨by simp, by simp⟩).symm
      map_comp := fun {a b c} φ ψ ↦ (hu a c _ _ ⟨by
        rw [← Category.assoc, (hm a b _).1, Category.assoc, (hm b c _).1, Category.assoc], by
        rw [← Category.assoc, (hm a b _).2, (hm b c _).2]⟩).symm }
  let θ : 𝟭 D ⟶ Q := { app := i, naturality := fun a b φ ↦ (hm a b _).1.symm }
  let η : (Functor.const D).obj d ⟶ Q :=
    { app := j, naturality := fun a b φ ↦ (Category.id_comp _).trans (hm a b _).2.symm }
  exact acyc_of_zigzag d ((Zigzag.of_hom θ).trans (Zigzag.of_inv η))
end FubiniStudyChowHeightFormula₂.Adr
