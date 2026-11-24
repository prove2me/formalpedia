-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Theta_ZetaSevenHalvesBounds_prime_ne_bot_of_mem_52dcf1ff8f2b
-- status  : ACCEPTED   (prove)
-- author  : @grencez
-- created : 2026-11-24T05:39:45.858665+00:00
-- url     : https://prove2.me/submissions/5a1ad246-873a-4781-b0a4-d9ab47464042

import Mathlib
open NumberField Ideal UniqueFactorizationMonoid
variable {K : Type*} [Field K] [NumberField K]


theorem solution {I P : Ideal (𝓞 K)} (h : P ∈ normalizedFactors I) :
    P.IsPrime ∧ P ≠ ⊥ := by
  have hp := prime_of_normalized_factor P h
  exact ⟨Ideal.isPrime_of_prime hp,hp.ne_zero⟩
