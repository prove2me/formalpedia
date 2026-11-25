-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_prod_pow_div_dvd_factorial_464682fa385a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T04:41:40.834568+00:00
-- url     : https://prove2.me/submissions/b66ce61d-9a68-4179-884e-23aa0d5339a9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PMertensUpper
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_div_le_padicValNat_factorial_9a940f801ab9

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open Real
namespace GroundTheory.Heights₂.Heights.Model
theorem _root_.solution (N : ℕ) :
    (∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p)) ∣ N.factorial := by
  have : ((∏ p ∈ (Finset.Iic N).filter Nat.Prime, p ^ (N / p) : ℕ) : ℤ) ∣ (N.factorial : ℤ) := by
    push_cast
    apply Finset.prod_dvd_of_coprime
    · intro p hp q hq hpq
      have hp' := (Finset.mem_filter.1 hp).2
      have hq' := (Finset.mem_filter.1 hq).2
      simp only [Function.onFun]
      exact_mod_cast Nat.isCoprime_iff_coprime.2 (Nat.coprime_pow_primes _ _ hp' hq' hpq)
    · intro p hp
      have hp' := (Finset.mem_filter.1 hp).2
      exact_mod_cast (pow_dvd_pow p (div_le_padicValNat_factorial N p hp')).trans
        pow_padicValNat_dvd
  exact_mod_cast this
end GroundTheory.Heights₂.Heights.Model
