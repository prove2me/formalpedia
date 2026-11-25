-- Prove2me | solution 1 for ReciprocityTheory.Cheb.log_norm_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:43:16.242392+00:00
-- url     : https://prove2.me/submissions/312eae2d-58eb-4c8c-92ae-efeb2433c6be

import Definitions.Def_ReciprocityTheory_Chebotarev_Support
import Definitions.Def_ReciprocityTheory_Chebotarev_AbsLogSubLogLeOfHalf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units NumberField.InfinitePlace
  NumberField.Units.dirichletUnitTheorem
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {z : mixedSpace E} (hz : ∀ w, normAtPlace w z ≠ 0) :
    Real.log (mixedEmbedding.norm z) = ∑ w, (mult w : ℝ) * Real.log (normAtPlace w z) := by
  rw [mixedEmbedding.norm_apply, Real.log_prod (fun w _ => pow_ne_zero _ (hz w))]
  simp_rw [Real.log_pow]
end ReciprocityTheory.Cheb
