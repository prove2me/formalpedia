-- Prove2me | solution 1 for ReciprocityTheory.Cheb.cyor_norm_cpow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:58:19.036879+00:00
-- url     : https://prove2.me/submissions/ee0f102f-1f4e-482f-9e38-3c3a76571992

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Theorems.Thm_ReciprocityTheory_Cheb_cyor_nrm_pos

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution (q : Prm E) (s : ℝ) :
    ‖((Nrm q : ℕ) : ℂ) ^ (-(s : ℂ))‖ = ((Nrm q : ℕ) : ℝ) ^ (-s) := by
  rw [Complex.norm_natCast_cpow_of_pos (cyor_nrm_pos q)]
  simp
end ReciprocityTheory.Cheb
