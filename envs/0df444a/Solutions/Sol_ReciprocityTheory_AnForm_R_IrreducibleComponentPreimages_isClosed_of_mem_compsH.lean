-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages.isClosed_of_mem_compsH
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:27:16.173675+00:00
-- url     : https://prove2.me/submissions/be0d6b80-fbd0-49dc-aeca-e11bee0e3786

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
theorem _root_.solution {T : Set α} (hT : IsClosed T) {C : Set α} (hC : C ∈ compsH T) :
    IsClosed C := by
  have h2 : closure C ⊆ C := hC.2 ⟨hC.1.1.closure, closure_minimal hC.1.2 hT⟩ subset_closure
  exact closure_subset_iff_isClosed.mp h2
end ReciprocityTheory.AnForm.R.IrreducibleComponentPreimages
