-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.lfa_mul_of_not_disjoint
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:22:39.372543+00:00
-- url     : https://prove2.me/submissions/a5a5f095-9ca3-4c99-bc01-2e06c44291dd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_CFPrimeA
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_LowFockA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (s t : Finset (Fin (n * n))) (h : ¬ Disjoint s t) :
    fockBasis n s * fockBasis n t = 0 := by
  exact ExteriorAlgebra.basis_mul_of_not_disjoint _ (Set.powersetCard.ofCard (rfl : s.card = s.card))
    (Set.powersetCard.ofCard (rfl : t.card = t.card)) h
end ReciprocityTheory.ChartRestriction.DS
