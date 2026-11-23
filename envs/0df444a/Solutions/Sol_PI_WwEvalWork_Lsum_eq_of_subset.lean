-- Prove2me | solution 1 for PI.WwEvalWork.Lsum_eq_of_subset
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:00:32.035934+00:00
-- url     : https://prove2.me/submissions/6730b12c-3d09-4c9d-bf04-c4ee6d572e01

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_WwEval
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LFunctionEvaluation_LsumEqOfSubset

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
theorem _root_.solution (w : (σ →₀ ℕ) → K) (Q : MvPolynomial σ K) (S : Finset (σ →₀ ℕ))
    (h : Q.support ⊆ S) : Lsum w Q = ∑ α ∈ S, coeff α Q * w α := by
  unfold Lsum
  apply Finset.sum_subset h
  intro α _ hα
  rw [notMem_support_iff.mp hα, zero_mul]
end PI.WwEvalWork
