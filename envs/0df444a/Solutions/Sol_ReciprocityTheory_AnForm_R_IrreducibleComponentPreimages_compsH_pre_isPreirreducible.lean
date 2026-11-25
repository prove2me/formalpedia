-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_pre_isPreirreducible
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:10:25.165589+00:00
-- url     : https://prove2.me/submissions/077b0848-60a9-4852-8665-dd9c4c039f96

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing
variable {α : Type*} [TopologicalSpace α]
namespace ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
theorem _root_.solution {T C : Set α} (hCT : C ⊆ T) (hC : IsPreirreducible C) :
    IsPreirreducible ((Subtype.val ⁻¹' C : Set T)) := by
  rw [isPreirreducible_iff_isClosed_union_isClosed] at hC ⊢
  intro z₁ z₂ h₁ h₂ hsub
  obtain ⟨Z₁, hZ₁, rfl⟩ := isClosed_induced_iff.mp h₁
  obtain ⟨Z₂, hZ₂, rfl⟩ := isClosed_induced_iff.mp h₂
  have hC' : C ⊆ Z₁ ∪ Z₂ := fun c hc => hsub (show (⟨c, hCT hc⟩ : T) ∈ Subtype.val ⁻¹' C from hc)
  rcases hC Z₁ Z₂ hZ₁ hZ₂ hC' with h | h
  · exact Or.inl (fun x hx => h hx)
  · exact Or.inr (fun x hx => h hx)
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
