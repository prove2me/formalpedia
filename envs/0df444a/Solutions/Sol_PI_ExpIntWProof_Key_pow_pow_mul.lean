-- Prove2me | solution 1 for PI.ExpIntWProof.Key.pow_pow_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:26.839488+00:00
-- url     : https://prove2.me/submissions/11fa002b-b279-4d0e-895d-b36c7aba3e2f

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
namespace PI.ExpIntWProof.Key
theorem _root_.solution {R : Type*} [CommRing R] (a : R) (p f : ℕ) (h : a ^ p ^ f = a) :
    ∀ k : ℕ, a ^ p ^ (f * k) = a
  | 0 => by simp
  | k + 1 => by
      rw [Nat.mul_succ, pow_add, pow_mul, solution a p f h k, h]
end PI.ExpIntWProof.Key
