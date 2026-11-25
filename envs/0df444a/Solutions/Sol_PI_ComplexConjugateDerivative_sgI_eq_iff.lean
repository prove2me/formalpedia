-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.sgI_eq_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:34:51.859607+00:00
-- url     : https://prove2.me/submissions/0d408be7-c9e5-4dac-8fa2-2beefa5a5d5e

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
theorem _root_.solution (i : Fin (2 * r + k + 1)) : sgI k r i.val = r + k ↔ i.val = r + k := by
  have hi := i.isLt
  unfold sgI
  split_ifs <;> constructor <;> intro h <;> omega
end PI.ComplexConjugateDerivative
