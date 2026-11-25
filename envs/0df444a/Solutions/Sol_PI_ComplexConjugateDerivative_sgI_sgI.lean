-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.sgI_sgI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:58.714887+00:00
-- url     : https://prove2.me/submissions/c0a6b5e7-d8bf-48b0-960b-04d5bbc5fff7

import Definitions.Def_Formalism_HermitianCurvature_FiniteOrderIntersectionInSmooth
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSecondOrder_HasDerivAtDOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
noncomputable section
open PI PI.ComplexConjugateDerivative
open Formalism.QuantumDeterminants Formalism.FourierDecayAlt
variable {k r : ℕ}
namespace PI.ComplexConjugateDerivative
theorem _root_.solution (i : Fin (2 * r + k + 1)) : sgI k r (sgI k r i.val) = i.val := by
  have hi := i.isLt
  unfold sgI
  split_ifs <;> omega
end PI.ComplexConjugateDerivative
