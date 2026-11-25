-- Prove2me | solution 1 for PI.LatMinWork.norm_two_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T09:48:54.8396+00:00
-- url     : https://prove2.me/submissions/074eed77-8cce-41f5-8fcd-0191e8e76707

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_LatMin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_MinimalLatticeNorm_NormTwoEqOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.LatMinWork
variable {p : ℕ} [hp : Fact p.Prime]
namespace PI.LatMinWork
theorem _root_.solution (hp2 : p ≠ 2) : ‖(2 : ℚ_[p])‖ = 1 := by
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).mp h')
  have h1 : ‖((2 : ℤ) : ℚ_[p])‖ ≤ 1 := by
    first
      | exact Padic.norm_int_le_one 2
      | exact padicNormE.norm_int_le_one 2
  have h3 : ¬ ‖((2 : ℤ) : ℚ_[p])‖ < 1 := fun h => h2 (by
    first
      | exact Padic.norm_intCast_lt_one_iff.mp h
      | exact (Padic.norm_int_lt_one_iff_dvd 2).1 h
      | exact (padicNormE.norm_int_lt_one_iff_dvd 2).1 h)
  have := le_antisymm h1 (not_lt.1 h3)
  exact_mod_cast this
end PI.LatMinWork
