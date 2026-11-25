-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.rw_eq_ev
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:48.273663+00:00
-- url     : https://prove2.me/submissions/c626070d-f8d3-4156-9612-199be8b17556

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_SmoothClassInFiniteOrder

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
theorem _root_.solution (v : List (B.Mat k r)) (F : B.Mat k r → E) :
    B.Rw v F = ev (List.replicate v.length false) v F := by
  induction v with
  | nil => rfl
  | cons X v ih =>
    show Formalism.REAL.RdV X (B.Rw v F) = D false X (ev (List.replicate v.length false) v F)
    rw [ih]; rfl
end PI.ComplexConjugateDerivative
