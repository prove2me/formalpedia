-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitC_nrm_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:45:47.357792+00:00
-- url     : https://prove2.me/submissions/c004db65-ef8b-46e9-be75-69d0ff593e17

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitC

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] (q : Prm E) : 0 < ((Nrm q : ℕ) : ℝ) := by
  have : Nrm q ≠ 0 := by
    unfold Nrm
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact q.ne_bot
  exact_mod_cast Nat.pos_of_ne_zero this
end ReciprocityTheory.Cheb
