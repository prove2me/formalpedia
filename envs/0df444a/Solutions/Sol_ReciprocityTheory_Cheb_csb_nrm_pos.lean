-- Prove2me | solution 1 for ReciprocityTheory.Cheb.csb_nrm_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:42:31.581461+00:00
-- url     : https://prove2.me/submissions/1cf51baa-216e-4c7e-b3c4-c9b897c672af

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitA
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitB

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] (q : Prm E) : 1 ≤ Nrm q := by
  unfold Nrm
  rw [Nat.one_le_iff_ne_zero, Ne, Ideal.absNorm_eq_zero_iff]
  exact q.ne_bot
end ReciprocityTheory.Cheb
