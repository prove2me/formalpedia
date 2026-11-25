-- Prove2me | solution 1 for ReciprocityTheory.Cheb.norm_psum_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:44:51.103433+00:00
-- url     : https://prove2.me/submissions/c720ec96-8f5a-4fd9-ae01-7d39b39dda64

import Definitions.Def_ReciprocityTheory_Chebotarev_NZIdeal
import Definitions.Def_ReciprocityTheory_Chebotarev_CycOrth
import Theorems.Thm_ReciprocityTheory_Cheb_cyor_term_norm_le
import Theorems.Thm_ReciprocityTheory_Cheb_cyor_summable

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
theorem _root_.solution {l : ℕ} (χ : DirichletCharacter ℂ l) (s : ℝ)
    (hS : Summable (fun q : Prm E => ((Nrm q : ℕ) : ℝ) ^ (-s))) :
    ‖Psum E χ s‖ ≤ PE E s := by
  unfold Psum PE
  refine (norm_tsum_le_tsum_norm (cyor_summable χ s hS).norm).trans ?_
  exact Summable.tsum_le_tsum (fun q => cyor_term_norm_le χ q s) (cyor_summable χ s hS).norm hS
end ReciprocityTheory.Cheb
