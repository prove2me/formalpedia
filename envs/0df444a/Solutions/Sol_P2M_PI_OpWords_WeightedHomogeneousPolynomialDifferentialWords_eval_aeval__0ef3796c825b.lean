-- Prove2me | solution 1 for P2M_PI_OpWords_WeightedHomogeneousPolynomialDifferentialWords_eval_aeval__0ef3796c825b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:56:40.065354+00:00
-- url     : https://prove2.me/submissions/412f62b9-fa24-410b-9d59-a83acf451305

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_KappaRight
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_PolynomialDifferentialWords_IsWeightedHomogeneousPairingLeft

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
theorem _root_.solution (g : Fin k ⊕ Fin k → Pol K k) (p : Fin k ⊕ Fin k → K) (f : Pol K k) :
    eval p (aeval g f) = eval (fun v => eval p (g v)) f := by
  induction f using MvPolynomial.induction_on <;> simp_all
end PI.OpWords.WeightedHomogeneousPolynomialDifferentialWords
