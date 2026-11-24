-- Prove2me | solution 1 for PI.ComplexConjugateDerivative.good_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T15:42:10.950956+00:00
-- url     : https://prove2.me/submissions/1c74a422-a4ed-4e72-ae51-6701cca4ffea

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
theorem _root_.solution : Good (k := k) (r := r) (E := E) id :=
  ⟨fun _ _ h g hg => h g hg, fun _ _ _ _ _ _ => rfl, fun _ _ _ _ _ => rfl⟩
end PI.ComplexConjugateDerivative
