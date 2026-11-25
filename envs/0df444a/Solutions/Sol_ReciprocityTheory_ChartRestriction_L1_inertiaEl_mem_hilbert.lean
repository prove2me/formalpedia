-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.inertiaEl_mem_hilbert
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:44:18.250813+00:00
-- url     : https://prove2.me/submissions/429d79ac-61f0-4f7d-90c4-25a6dd1bac93

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_ModGBasic
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_inertiaEl_iff

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω] {A : ValuationSubring Ω}
    {g : Ω ≃ₐ[E] Ω} (h : InertiaEl A g) : g ∈ hilbertSubgroup E Ω := by
  unfold hilbertSubgroup
  exact Subgroup.le_topologicalClosure _
    (Subgroup.subset_closure (Or.inl (Or.inr ⟨A, (inertiaEl_iff A g).1 h⟩)))
end ReciprocityTheory.ChartRestriction.L1
