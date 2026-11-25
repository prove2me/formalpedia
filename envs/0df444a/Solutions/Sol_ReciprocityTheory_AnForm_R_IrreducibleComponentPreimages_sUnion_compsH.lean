-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.sUnion_compsH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:32.223971+00:00
-- url     : https://prove2.me/submissions/8646d886-abbc-4b55-bbfd-afe1b8d747e9

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_image_mem_compsH

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
theorem _root_.solution (T : Set α) : ⋃₀ compsH T = T := by
  apply Set.Subset.antisymm
  · rintro x ⟨C, hC, hx⟩
    exact hC.1.2 hx
  · intro x hx
    exact ⟨Subtype.val '' irreducibleComponent (⟨x, hx⟩ : T),
      image_mem_compsH (irreducibleComponent_mem_irreducibleComponents _),
      ⟨⟨x, hx⟩, mem_irreducibleComponent, rfl⟩⟩
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
