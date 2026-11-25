-- Prove2me | solution 1 for ReciprocityTheory.Cheb.card_primesOverFinset_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:12.342019+00:00
-- url     : https://prove2.me/submissions/897321c8-d752-4cac-b329-42a26df84db4

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycTail

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
theorem _root_.solution (p : ℕ) (hp : p.Prime) :
    (IsDedekindDomain.primesOverFinset (Ideal.span {(p:ℤ)}) (𝓞 E)).card ≤ Module.finrank ℚ E := by
  have : (Ideal.span {(p:ℤ)}).IsMaximal :=
    ((Ideal.span_singleton_prime (by exact_mod_cast hp.ne_zero)).mpr
      (Nat.prime_iff_prime_int.mp hp)).isMaximal (by simp [hp.ne_zero])
  exact Ideal.card_primesOverFinset_le_finrank (𝓞 E) ℚ E (by simp [hp.ne_zero])
end ReciprocityTheory.Cheb
