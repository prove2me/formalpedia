-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homS_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:52:39.053999+00:00
-- url     : https://prove2.me/submissions/4c09c461-6ec3-437f-aef3-8e1b0257444d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
import Theorems.Thm_Formalism_ELL_FormalGroupQuadraticJets_hb


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
variable {K : Type} [Field K] (U : PowerSeries K)
namespace ReciprocityTheory.ChartRestriction.L1
theorem _root_.solution (m i : ℕ) (hi : i ≤ m) (a : K) :
    homS U m (monomial i a) = PowerSeries.C a * U ^ i * PowerSeries.X ^ (2 * (m - i)) := by
  unfold homS
  rw [Finset.sum_eq_single i]
  · simp
  · intro b _ hb
    rw [coeff_monomial, if_neg (Ne.symm hb)]
    simp
  · intro h
    exact absurd (Finset.mem_range.2 (Nat.lt_succ_of_le hi)) h
end ReciprocityTheory.ChartRestriction.L1
