-- Prove2me | solution 1 for ReciprocityTheory.Cheb.natCast_cpow_mul_cpow_neg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:42:44.818256+00:00
-- url     : https://prove2.me/submissions/b5a62e9e-ab3b-4357-ad34-f56c7229b14d

import Definitions.Def_ReciprocityTheory_Chebotarev_NormGsEmbZLe
import Definitions.Def_ReciprocityTheory_Chebotarev_RpowNegFinrankSubOne
import Definitions.Def_ReciprocityTheory_Chebotarev_IdealLat
import Definitions.Def_ReciprocityTheory_Chebotarev_MeanZero
import Definitions.Def_ReciprocityTheory_Chebotarev_LatSum
import Definitions.Def_ReciprocityTheory_Chebotarev_KHoldA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField NumberField.mixedEmbedding NumberField.Units Set
open scoped Classical
open ReciprocityTheory ReciprocityTheory.Cheb
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.Cheb
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) (s : ℂ) : (n : ℂ) ^ s * (n : ℂ) ^ (-s) = 1 := by
  rw [Complex.cpow_neg, mul_inv_cancel₀]
  rw [Ne, Complex.cpow_eq_zero_iff]
  exact fun h => hn (by exact_mod_cast h.1)
end ReciprocityTheory.Cheb
