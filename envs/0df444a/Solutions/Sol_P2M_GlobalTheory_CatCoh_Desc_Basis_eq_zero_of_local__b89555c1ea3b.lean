-- Prove2me | solution 1 for P2M_GlobalTheory_CatCoh_Desc_Basis_eq_zero_of_local__b89555c1ea3b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:39:31.066648+00:00
-- url     : https://prove2.me/submissions/41f18f66-2b9b-4459-a3f7-faf9029052dd

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ComparisonMemCechHodgeFiltration
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_VanishingH1InvertingMorphisms
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_OneCocycleCoboundaryCommaLocalBasis
import Theorems.Thm_GlobalTheory_CatCoh_Desc_Basis_eq_zero_of_local

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
open CategoryTheory AlgebraicGeometry KaehlerDifferential ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.CechDR
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.CatCoh.Desc GlobalTheory.CatCoh.Desc.Basis
variable {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C']
namespace GlobalTheory.CatCoh.Desc.Basis
theorem _root_.solution (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C) (H : HasLoc F)
    (hdir : (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S),
      Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) →
        ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')))
    {t₁ t₂ t₃ : C'} {S : C} (h₁ : Nonempty (G.obj t₁ ⟶ S)) (h₂ : Nonempty (G.obj t₂ ⟶ S))
    (h₃ : Nonempty (G.obj t₃ ⟶ S)) (z : F.obj S)
    (hz : ∀ t (S' : C) (ψ : S ⟶ S'), Nonempty (t₁ ⟶ t) → Nonempty (t₂ ⟶ t) → Nonempty (t₃ ⟶ t) →
      Nonempty (G.obj t ⟶ S') → mp F ψ z = 0) : z = 0 := by
  refine eq_zero_of_local F G H hdir h₁ h₂ z fun t S' ψ h1 h2 ⟨w⟩ ↦ ?_
  obtain ⟨w₃⟩ := h₃
  obtain ⟨a1⟩ := h1
  obtain ⟨a2⟩ := h2
  refine eq_zero_of_local F G H hdir ⟨w⟩ ⟨w₃ ≫ ψ⟩ _ fun t' S'' χ ⟨a⟩ h3 h4 ↦ ?_
  rw [← mp_comp]
  exact hz t' S'' (ψ ≫ χ) ⟨a1 ≫ a⟩ ⟨a2 ≫ a⟩ h3 h4
end GlobalTheory.CatCoh.Desc.Basis
