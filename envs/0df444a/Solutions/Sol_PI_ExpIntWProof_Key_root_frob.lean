-- Prove2me | solution 1 for PI.ExpIntWProof.Key.root_frob
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:37:53.737855+00:00
-- url     : https://prove2.me/submissions/577463be-955a-43cd-b086-753111ea1f4e

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
variable {p : ℕ} [hp : Fact p.Prime]
namespace PI.ExpIntWProof.Key
theorem _root_.solution {x : ℂ_[p]} {n : ℕ} (_hn : 0 < n) (hc : Nat.Coprime n p) (hx : x ^ n = 1) :
    x ^ p ^ Nat.totient n = x := by
  have hred : ∀ a : ℕ, x ^ a = x ^ (a % n) := fun a => by
    conv_lhs => rw [← Nat.div_add_mod a n]
    rw [pow_add, pow_mul, hx, one_pow, one_mul]
  have hmod : p ^ Nat.totient n % n = 1 % n := Nat.ModEq.pow_totient hc.symm
  rw [hred, hmod, ← hred, pow_one]
end PI.ExpIntWProof.Key
