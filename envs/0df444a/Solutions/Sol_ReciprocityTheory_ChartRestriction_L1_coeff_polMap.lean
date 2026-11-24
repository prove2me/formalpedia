-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.coeff_polMap
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T22:08:22.325146+00:00
-- url     : https://prove2.me/submissions/a81c2587-8d81-4f07-8e8f-4d8e532f95ae

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProj

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.L1
variable {E : Type} [Field E]
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (ψ : E →+ E) (m : ℕ) (Q : E[X]) (i : ℕ) :
    (polMap ψ m Q).coeff i = if i ≤ m then ψ (Q.coeff i) else 0 := by
  simp only [polMap, finsetSum_coeff, coeff_monomial]
  rw [Finset.sum_ite_eq' (Finset.range (m + 1)) i]
  simp
end ReciprocityTheory.ChartRestriction.L1
