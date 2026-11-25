-- Prove2me | solution 1 for P2M_FubiniStudyChowHeightFormula__Adr_cm_zigzag_e21921fb67fd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:49:00.159225+00:00
-- url     : https://prove2.me/submissions/a0f58d66-2955-4e9a-899b-13cfad686e89

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_CommAlgFunctorCoboundaryZeroMemCocyclesOne
import Definitions.Def_Development_WeilBound_CoreStatements_AbelianHeightsDuality_DividedPowerAlgebras_AcycOfCoprod
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyOne_eq_of_natTrans
import Theorems.Thm_GlobalTheory_CatCoh_CoefMap_pullCohomologyTwo_eq_of_natTrans


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
theorem _root_.solution (M : CommAlgCat.{0} R) {G G' : D ⥤ D} (h : Zigzag G G') :
    (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a, g (G.obj a) = g (G'.obj a)) ∧
    (∀ c, (cm M G).pull1 c = (cm M G').pull1 c) ∧ ∀ c, (cm M G).pull2 c = (cm M G').pull2 c := by
  have one : ∀ {G G' : D ⥤ D} (_ : G ⟶ G'),
      (∀ g : D → M, (∀ a b (_ : a ⟶ b), g b = g a) → ∀ a, g (G.obj a) = g (G'.obj a)) ∧
      (∀ c, (cm M G).pull1 c = (cm M G').pull1 c) ∧ ∀ c, (cm M G).pull2 c = (cm M G').pull2 c :=
    fun {G G'} θ ↦ ⟨fun g hg a ↦ (hg _ _ (θ.app a)).symm,
      (cm M G).pullCohomologyOne_eq_of_natTrans (cm M G') θ fun _ _ ↦ rfl,
      (cm M G).pullCohomologyTwo_eq_of_natTrans (cm M G') θ fun _ _ ↦ rfl⟩
  induction h with
  | refl => exact ⟨fun _ _ _ ↦ rfl, fun _ ↦ rfl, fun _ ↦ rfl⟩
  | tail _ hz ih =>
    rcases hz with ⟨⟨θ⟩⟩ | ⟨⟨θ⟩⟩
    · exact ⟨fun g hg a ↦ (ih.1 g hg a).trans ((one θ).1 g hg a), fun c ↦ (ih.2.1 c).trans ((one θ).2.1 c),
        fun c ↦ (ih.2.2 c).trans ((one θ).2.2 c)⟩
    · exact ⟨fun g hg a ↦ (ih.1 g hg a).trans ((one θ).1 g hg a).symm,
        fun c ↦ (ih.2.1 c).trans ((one θ).2.1 c).symm, fun c ↦ (ih.2.2 c).trans ((one θ).2.2 c).symm⟩
end FubiniStudyChowHeightFormula₂.Adr
