-- Prove2me | solution 1 for ReciprocityTheory.Cheb.two_le_nrm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:26:56.675855+00:00
-- url     : https://prove2.me/submissions/70d1dec0-b072-45f0-8dce-1ae684248815

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
theorem _root_.solution (q : Prm E) : 2 ≤ Nrm q := by
  have h0 : Nrm q ≠ 0 := by
    unfold Nrm; rw [Ne, Ideal.absNorm_eq_zero_iff]; exact q.ne_bot
  have h1 : Nrm q ≠ 1 := by
    unfold Nrm; rw [Ne, Ideal.absNorm_eq_one_iff]; exact q.isPrime.ne_top
  omega
end ReciprocityTheory.Cheb
