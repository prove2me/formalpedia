-- Prove2me | solution 1 for PI.WwEvalWork.Lsum_monomial
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:23:03.794856+00:00
-- url     : https://prove2.me/submissions/855829a0-8759-43c2-ba8b-6f6f1b9cf3aa

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
theorem _root_.solution (w : (σ →₀ ℕ) → K) (α : σ →₀ ℕ) (r : K) :
    Lsum w (monomial α r) = r * w α := by
  classical
  rw [Lsum_eq_of_subset w _ {α} support_monomial_subset, Finset.sum_singleton, coeff_monomial,
    if_pos rfl]
end PI.WwEvalWork
