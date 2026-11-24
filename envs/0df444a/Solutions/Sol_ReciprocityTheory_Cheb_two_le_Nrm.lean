-- Prove2me | solution 1 for ReciprocityTheory.Cheb.two_le_Nrm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:08:13.051184+00:00
-- url     : https://prove2.me/submissions/c7859ce2-72db-4ffb-a3a0-510b891d260b

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_EulerSum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Filter Topology
open ReciprocityTheory ReciprocityTheory.Cheb
namespace ReciprocityTheory.Cheb
theorem _root_.solution {E : Type} [Field E] [NumberField E] (q : Prm E) : 2 ≤ Nrm q := by
  have h0 : Ideal.absNorm q.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact q.ne_bot
  have h1 : Ideal.absNorm q.asIdeal ≠ 1 := by
    rw [Ne, Ideal.absNorm_eq_one_iff]
    exact q.isPrime.ne_top
  unfold Nrm
  omega
end ReciprocityTheory.Cheb
