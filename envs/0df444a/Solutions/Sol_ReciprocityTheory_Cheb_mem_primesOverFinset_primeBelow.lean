-- Prove2me | solution 1 for ReciprocityTheory.Cheb.mem_primesOverFinset_primeBelow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:31.709493+00:00
-- url     : https://prove2.me/submissions/6c3801f4-2bef-4a36-b02b-ab00ce940ff7

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail
import Theorems.Thm_ReciprocityTheory_Cheb_primeBelow_prime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (q : Prm E) :
    q.asIdeal ∈ IsDedekindDomain.primesOverFinset (Ideal.span {((primeBelow q : ℕ) : ℤ)}) (𝓞 E) := by
  have hp := primeBelow_prime q
  have : (Ideal.span {((primeBelow q : ℕ) : ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  rw [IsDedekindDomain.mem_primesOverFinset_iff (by simp [hp.ne_zero])]
  exact ⟨q.isPrime, Int.liesOver_span_absNorm q.asIdeal⟩
end ReciprocityTheory.Cheb
