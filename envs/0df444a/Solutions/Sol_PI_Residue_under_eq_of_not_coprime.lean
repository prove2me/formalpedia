-- Prove2me | solution 1 for PI.Residue.under_eq_of_not_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:13:58.574142+00:00
-- url     : https://prove2.me/submissions/cec45417-a28f-4bd3-a510-15b6d9926a4c

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_FactorizationMultisetProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ResidueLatticeCount_UnderEqOfNotCoprime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PI PI.Residue
open NumberField Ideal UniqueFactorizationMonoid
open scoped ENNReal
variable (E : Type*) [Field E] [NumberField E]
variable {E}
variable (E)
variable {E}
namespace PI.Residue
theorem _root_.solution {P Q : Ideal (𝓞 E)} (hP : P ∈ primeSet E) (hQ : Q ∈ primeSet E)
    (hcop : ¬ Nat.Coprime (absNorm P) (absNorm Q)) : P.under ℤ = Q.under ℤ := by
  have := hP.1
  have := hQ.1
  have : NeZero P := ⟨hP.2⟩
  have : NeZero Q := ⟨hQ.2⟩
  have pP := Nat.absNorm_under_prime P
  have pQ := Nat.absNorm_under_prime Q
  have eP := absNorm_eq_pow_inertiaDeg'_of_liesOver P (P.under ℤ) inferInstance
    (Ideal.under_ne_bot ℤ hP.2)
  have eQ := absNorm_eq_pow_inertiaDeg'_of_liesOver Q (Q.under ℤ) inferInstance
    (Ideal.under_ne_bot ℤ hQ.2)
  by_contra hne
  apply hcop
  rw [eP, eQ]
  apply Nat.Coprime.pow
  rw [Nat.coprime_primes pP pQ]
  intro heq
  apply hne
  rw [← Int.ideal_span_absNorm_eq_self (P.under ℤ), ← Int.ideal_span_absNorm_eq_self (Q.under ℤ),
    heq]
end PI.Residue
