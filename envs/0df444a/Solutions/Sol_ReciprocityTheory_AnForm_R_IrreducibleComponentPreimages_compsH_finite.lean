-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.compsH_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:34:09.052641+00:00
-- url     : https://prove2.me/submissions/b76ce441-526d-4865-b277-9771b042d566

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_Monomial
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_FinalTheorems
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_PreMemIrreducibleComponents
import Theorems.Thm_ReciprocityTheory_AnForm_R_IrreducibleComponentPreimages_pre_mem_irreducibleComponents

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
theorem _root_.solution [NoetherianSpace α] (T : Set α) : (compsH T).Finite := by
  have hfin : (irreducibleComponents T).Finite := NoetherianSpace.finite_irreducibleComponents
  refine (hfin.image (Set.image Subtype.val)).subset fun C hC =>
    ⟨Subtype.val ⁻¹' C, pre_mem_irreducibleComponents hC, ?_⟩
  exact Set.image_preimage_eq_of_subset (by rw [Subtype.range_coe]; exact hC.1.2)
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
