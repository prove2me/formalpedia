-- Prove2me | solution 1 for ReciprocityTheory.Cheb.re_psum_one_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T15:06:15.786362+00:00
-- url     : https://prove2.me/submissions/ceb6704d-aaea-4845-87aa-28d20fe99376

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Theorems.Thm_ReciprocityTheory_Cheb_norm_psum_le

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
theorem _root_.solution (l : ℕ) [NeZero l] (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    (Psum E (1 : DirichletCharacter ℂ l) s).re ≤ PE E s :=
  (Complex.re_le_norm _).trans (norm_psum_le _ s hS)
end ReciprocityTheory.Cheb
