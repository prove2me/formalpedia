-- Prove2me | solution 1 for PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords.not_X_dvd_tt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:00:46.595473+00:00
-- url     : https://prove2.me/submissions/9d9bbd60-2afc-49d3-8679-f72b75593c41

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft
import Theorems.Thm_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_eval_tt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open PI PI.OpWords PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
variable {K : Type} [Field K] [CharZero K] {k : ℕ}
namespace PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
theorem _root_.solution (i0 j : Fin k) (hj : j ≠ i0) :
    ¬ (X (Sum.inl i0) : Pol K k) ∣ tt K k := by
  rintro ⟨q, hq⟩
  have h := congrArg (eval (Sum.elim (fun i : Fin k => if i = j then (1 : K) else 0) (fun _ => 1))) hq
  rw [eval_tt] at h
  simp [Ne.symm hj] at h
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
