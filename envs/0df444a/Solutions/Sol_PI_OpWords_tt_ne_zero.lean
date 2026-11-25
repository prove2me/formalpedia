-- Prove2me | solution 1 for PI.OpWords.tt_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:02:10.298865+00:00
-- url     : https://prove2.me/submissions/45c9c577-951b-4150-8daa-bdebe234855d

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_PolarizationBihomogeneous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Finsupp
noncomputable section
open PI PI.OpWords
namespace PI.OpWords
theorem _root_.solution (K : Type) [Field K] [CharZero K] (k : ℕ) (hk : 0 < k) : tt K k ≠ 0 := by
  intro h
  have h1 := congrArg (eval (fun _ : Fin k ⊕ Fin k => (1 : K))) h
  simp [tt] at h1
  omega
end PI.OpWords
