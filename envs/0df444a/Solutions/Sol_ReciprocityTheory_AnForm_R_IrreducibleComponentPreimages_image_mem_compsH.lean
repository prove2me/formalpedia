-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.image_mem_compsH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:47.765542+00:00
-- url     : https://prove2.me/submissions/72412c95-083e-4d17-beff-51ff09084f7d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_compsH_pre_isIrreducible

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
theorem _root_.solution {T : Set α} {A : Set T} (hA : A ∈ irreducibleComponents T) :
    Subtype.val '' A ∈ compsH T := by
  refine ⟨⟨hA.1.image _ continuous_subtype_val.continuousOn, by rintro _ ⟨x, _, rfl⟩; exact x.2⟩, ?_⟩
  intro C' hC' hle
  have h1 : A ⊆ Subtype.val ⁻¹' C' := fun x hx => hle ⟨x, hx, rfl⟩
  have h2 := hA.2 (compsH_pre_isIrreducible hC'.2 hC'.1) h1
  intro c hc
  exact ⟨⟨c, hC'.2 hc⟩, h2 hc, rfl⟩
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
