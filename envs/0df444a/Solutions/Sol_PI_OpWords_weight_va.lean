-- Prove2me | solution 1 for PI.OpWords.weight_va
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:02:03.912913+00:00
-- url     : https://prove2.me/submissions/99b0619b-4e33-4c5b-836e-cb1f30514323

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
theorem _root_.solution (k : ℕ) (a : Fin k) (m : Fin k ⊕ Fin k →₀ ℕ) :
    weight (va k a) m = (m (Sum.inl a) : ℤ) - m (Sum.inr a) := by
  simp [Finsupp.weight_apply, Finsupp.sum_fintype, va, Fintype.sum_sum_type, sub_eq_add_neg]
end PI.OpWords
