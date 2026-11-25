-- Prove2me | solution 1 for ReciprocityTheory.Cheb.rpow_neg_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:51:30.376772+00:00
-- url     : https://prove2.me/submissions/7e29afb8-9fa2-41a5-a202-78084ca5f66b

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
theorem _root_.solution {s m N : ℝ} (hs : 1 ≤ s) (hm : 1 ≤ m) (hN : m ≤ N) : N ^ (-s) ≤ m⁻¹ := by
  calc N ^ (-s) ≤ N ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    _ = N⁻¹ := Real.rpow_neg_one N
    _ ≤ m⁻¹ := inv_anti₀ (by linarith) hN
end ReciprocityTheory.Cheb
