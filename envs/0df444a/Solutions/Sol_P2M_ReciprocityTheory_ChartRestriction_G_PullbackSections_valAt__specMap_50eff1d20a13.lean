-- Prove2me | solution 1 for P2M_ReciprocityTheory_ChartRestriction_G_PullbackSections_valAt__specMap_50eff1d20a13
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T15:15:06.834162+00:00
-- url     : https://prove2.me/submissions/ef24163c-e3b8-47ad-a6bd-321df67055d3

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PullbackSections_HolomorphicFamilies_HolPairB
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
set_option autoImplicit false
noncomputable section
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
private theorem valAt'_comp_lemma {Y Y' : Scheme.{0}} (x : Sp ℂ ⟶ Y) (φ : Y ⟶ Y') (U : Y'.Opens)
    (f : Γ(Y', U)) : valAt' x (φ ⁻¹ᵁ U) (φ.app U f) = valAt' (x ≫ φ) U f := by
  unfold valAt'
  by_cases h : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ U
  · have h' : ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_pos h', dif_pos h]
    unfold valAt
    first
      | (rw [Scheme.comp_appLE]) <;> rfl
      | (rw [Scheme.Hom.comp_appLE]) <;> rfl
      | simp [Scheme.comp_appLE]
  · have h' : ¬ ⊤ ≤ x ⁻¹ᵁ (φ ⁻¹ᵁ U) := h
    rw [dif_neg h', dif_neg h]
end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.PullbackSections
open AlgebraicGeometry CategoryTheory Limits Opposite ReciprocityTheory.ChartRestriction.G.TB.ValAt ReciprocityTheory.ChartRestriction.G.Geo.Tor TensorProduct
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace ReciprocityTheory.ChartRestriction.G.PullbackSections
theorem _root_.solution {A C : CommRingCat.{0}} (φ : A ⟶ C) (x : Sp ℂ ⟶ Spec C) (a : A) :
    valAt' (x ≫ Spec.map φ) ⊤ ((Scheme.ΓSpecIso A).inv a) = valAt' x ⊤ ((Scheme.ΓSpecIso C).inv (φ a)) := by
  have key : (Spec.map φ).app ⊤ ((Scheme.ΓSpecIso A).inv a) = (Scheme.ΓSpecIso C).inv (φ a) := by
    first
      | exact (congrArg (fun g : A ⟶ Γ(Spec C, ⊤) => g a) (Scheme.ΓSpecIso_inv_naturality φ)).symm
      | simp
  (rw [← valAt'_comp_lemma, key]) <;> rfl
end ReciprocityTheory.ChartRestriction.G.PullbackSections
