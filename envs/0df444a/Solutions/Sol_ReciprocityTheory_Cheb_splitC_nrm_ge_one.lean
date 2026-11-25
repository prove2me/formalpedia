-- Prove2me | solution 1 for ReciprocityTheory.Cheb.splitC_nrm_ge_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:06:02.525234+00:00
-- url     : https://prove2.me/submissions/f98c4546-943e-4ce5-8e92-e3a6aea0a5da

import Definitions.Def_ReciprocityTheory_Chebotarev_SplitDef
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitF
import Definitions.Def_ReciprocityTheory_Chebotarev_ChebyshevLambdaSubPsiBounded
import Definitions.Def_ReciprocityTheory_Chebotarev_SplitC
import Theorems.Thm_ReciprocityTheory_Cheb_splitC_nrm_pos

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
theorem _root_.solution {E : Type} [Field E] [NumberField E] (q : Prm E) : 1 ≤ ((Nrm q : ℕ) : ℝ) := by
  have h := splitC_nrm_pos q
  have : 0 < Nrm q := by exact_mod_cast h
  exact_mod_cast this
end ReciprocityTheory.Cheb
