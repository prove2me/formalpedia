-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.L1.homS_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:48:34.024566+00:00
-- url     : https://prove2.me/submissions/6e962df1-8e47-4c2e-a7d6-901af0d92b20

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_UnramifiedIntegrals_RedProjA

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
theorem _root_.solution (m : ℕ) (P Q : K[X]) : homS U m (P + Q) = homS U m P + homS U m Q := by
  simp only [homS, coeff_add, map_add, add_mul, Finset.sum_add_distrib]
end ReciprocityTheory.ChartRestriction.L1
