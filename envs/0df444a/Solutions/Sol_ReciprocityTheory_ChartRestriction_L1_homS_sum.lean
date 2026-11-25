-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homS_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:44.906829+00:00
-- url     : https://prove2.me/submissions/c2c86698-5b94-421c-bf7d-622c8579d47d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homS_add
import Theorems.Thm_ReciprocityTheory_ChartRestriction_L1_homS_zero

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
theorem _root_.solution {ι : Type} (s : Finset ι) (m : ℕ) (f : ι → K[X]) :
    homS U m (∑ i ∈ s, f i) = ∑ i ∈ s, homS U m (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [homS_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, homS_add, ih]
end ReciprocityTheory.ChartRestriction.L1
