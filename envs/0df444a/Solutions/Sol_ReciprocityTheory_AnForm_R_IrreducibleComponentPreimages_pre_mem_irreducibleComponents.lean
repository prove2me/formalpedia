-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.pre_mem_irreducibleComponents
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:24:52.931084+00:00
-- url     : https://prove2.me/submissions/d951f1a7-c9f4-402a-8ee6-f7fb0caec27f

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
theorem _root_.solution {T C : Set α} (hC : C ∈ compsH T) :
    (Subtype.val ⁻¹' C : Set T) ∈ irreducibleComponents T := by
  refine ⟨compsH_pre_isIrreducible hC.1.2 hC.1.1, ?_⟩
  intro B hB hle
  have h1 : C ⊆ Subtype.val '' B := fun c hc => ⟨⟨c, hC.1.2 hc⟩, hle hc, rfl⟩
  have h2 := hC.2 ⟨hB.image _ continuous_subtype_val.continuousOn, by rintro _ ⟨x, _, rfl⟩; exact x.2⟩ h1
  intro x hx
  exact h2 ⟨x, hx, rfl⟩
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
