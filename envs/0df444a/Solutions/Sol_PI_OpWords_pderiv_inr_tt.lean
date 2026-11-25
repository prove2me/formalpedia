-- Prove2me | solution 1 for PI.OpWords.pderiv_inr_tt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:06:50.408545+00:00
-- url     : https://prove2.me/submissions/307e6f96-91d1-4839-b4f6-ddf7e3d4f267

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
theorem _root_.solution (K : Type) [Field K] (k : ℕ) (a : Fin k) :
    pderiv (Sum.inr a) (tt K k) = X (Sum.inl a) := by
  simp [tt, Derivation.leibniz, pderiv_X, Pi.single_apply]
end PI.OpWords
