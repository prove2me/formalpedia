-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.dLR_eq_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:39:49.158362+00:00
-- url     : https://prove2.me/submissions/35fc6a6c-7967-4e93-bcf6-4bbde2e5fd0b

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder
import Theorems.Thm_PI_ComplexConjugateDerivative_rw_eq_ev

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
noncomputable section
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace PI.ComplexConjugateDerivative
theorem _root_.solution (u v : List (B.Mat k r)) (F : B.Mat k r → E) :
    B.dLR u v F = ev (List.replicate u.length true ++ List.replicate v.length false) (u ++ v) F := by
  induction u with
  | nil => exact rw_eq_ev v F
  | cons X u ih =>
    show B.LdV X (B.dLR u v F) = D true X (ev (List.replicate u.length true ++ List.replicate v.length false) (u ++ v) F)
    rw [ih]; rfl
end PI.ComplexConjugateDerivative
