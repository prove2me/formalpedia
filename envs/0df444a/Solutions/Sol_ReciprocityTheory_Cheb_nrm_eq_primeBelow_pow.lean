-- Prove2me | solution 1 for ReciprocityTheory.Cheb.nrm_eq_primeBelow_pow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:50:26.59267+00:00
-- url     : https://prove2.me/submissions/e542060f-391b-4b67-95b8-b51e5bd02c00

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
theorem _root_.solution (q : Prm E) : ∃ f : ℕ, Nrm q = primeBelow q ^ f :=
  have : q.asIdeal.LiesOver (Ideal.span {((primeBelow q : ℕ) : ℤ)}) := Int.liesOver_span_absNorm q.asIdeal
  ⟨_, Ideal.absNorm_eq_pow_inertiaDeg' q.asIdeal (primeBelow_prime q)⟩
end ReciprocityTheory.Cheb
