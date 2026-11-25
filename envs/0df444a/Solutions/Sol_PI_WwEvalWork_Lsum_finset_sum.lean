-- Prove2me | solution 1 for PI.WwEvalWork.Lsum_finset_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:31:10.635737+00:00
-- url     : https://prove2.me/submissions/94386df4-8e2e-4ac9-8b38-8a63a3188aa2

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset
import Theorems.Thm_PI_WwEvalWork_Lsum_add
import Theorems.Thm_PI_WwEvalWork_Lsum_zero

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
theorem _root_.solution {ι : Type*} (w : (σ →₀ ℕ) → K) (s : Finset ι)
    (f : ι → MvPolynomial σ K) : Lsum w (∑ i ∈ s, f i) = ∑ i ∈ s, Lsum w (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [Lsum_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Lsum_add, ih]
end PI.WwEvalWork
