-- Prove2me | solution 1 for ReciprocityTheory.AnForm.R.isClosed_of_mem_comps
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:30:18.796807+00:00
-- url     : https://prove2.me/submissions/f00a2787-f291-41ce-b08a-0b66d7d8f4b2

import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_StalkLoc
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_IsOpenAlt
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsMulMemOfAlgebraMapLocRingEqZero
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_ExistsBasicOpenCover

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.R
open AlgebraicGeometry CategoryTheory MvPolynomial TopologicalSpace IrreducibleComponentPreimages
noncomputable section
variable {α : Type*} [TopologicalSpace α]
namespace ReciprocityTheory.AnForm.R
theorem _root_.solution {T : Set α} (hT : IsClosed T) {C : Set α} (hC : C ∈ comps T) :
    IsClosed C := by
  have hC' : Maximal (fun C => IsIrreducible C ∧ C ⊆ T) C := hC
  have hcl : closure C ≤ C := hC'.2 ⟨hC'.1.1.closure, closure_minimal hC'.1.2 hT⟩ subset_closure
  exact closure_subset_iff_isClosed.1 hcl
end ReciprocityTheory.AnForm.R
