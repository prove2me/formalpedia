-- Prove2me | solution 1 for PI.WwEvalWork.Lsum_add
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:18:41.6865+00:00
-- url     : https://prove2.me/submissions/4c950a2b-f6a1-43b8-8dcd-e97f4f57d1bd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
import Theorems.Thm_PI_WwEvalWork_Lsum_eq_of_subset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WwEvalWork
open MvPolynomial
variable {σ K : Type*} [CommRing K]
namespace PI.WwEvalWork
theorem _root_.solution (w : (σ →₀ ℕ) → K) (p q : MvPolynomial σ K) :
    Lsum w (p + q) = Lsum w p + Lsum w q := by
  classical
  rw [Lsum_eq_of_subset w (p + q) (p.support ∪ q.support) support_add,
    Lsum_eq_of_subset w p (p.support ∪ q.support) Finset.subset_union_left,
    Lsum_eq_of_subset w q (p.support ∪ q.support) Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [coeff_add, add_mul]
end PI.WwEvalWork
