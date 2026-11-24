-- Prove2me | solution 1 for PI.ExpIntWProof.Key.Fx.neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T21:53:20.700853+00:00
-- url     : https://prove2.me/submissions/1973a877-710b-42a8-b4d6-bdadc3bb9db9

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExponentialIntegrality_RootsOfUnityRingLeWittIntegers

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.ExpIntWProof PI.ExpIntWProof.Key
variable {R : Type*} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]
namespace PI.ExpIntWProof.Key
namespace Fx
theorem _root_.solution {a : R} (ha : Fx p a) : Fx p (-a) := by
  obtain ⟨f, hf, h1⟩ := ha
  have : ExpChar R p := ExpChar.prime hp.out
  refine ⟨f, hf, ?_⟩
  rw [neg_eq_neg_one_mul, mul_pow, neg_one_pow_expChar_pow, h1]
end Fx
end PI.ExpIntWProof.Key
