-- Prove2me | solution 1 for ReciprocityTheory.Cheb.primeBelow_prime
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:20:22.122161+00:00
-- url     : https://prove2.me/submissions/fe67cbe2-aa3c-4e21-ae1e-23e84cefa77e

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
theorem _root_.solution (q : Prm E) : (primeBelow q).Prime := by
  have : NeZero q.asIdeal := ⟨q.ne_bot⟩
  exact Nat.absNorm_under_prime q.asIdeal
end ReciprocityTheory.Cheb
