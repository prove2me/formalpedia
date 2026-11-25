-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chowFormSwap_457535a64ce2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:43:01.161283+00:00
-- url     : https://prove2.me/submissions/f30bf4e0-28a5-451f-8772-ae022cf66fb3

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_RenameProdMapMul
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_rename_prodMap_mul_83bfca8ced4c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_rename_prodMap_one_85d5f711b452
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IsChowForm_rename_swap_1271ec25e150

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial
noncomputable section
variable {F : Type*} [Field F] {n k : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : ChowFormSwap.Statement := by
  intro F _ n k I f hf τ
  induction τ using Equiv.Perm.swap_induction_on with
  | one => exact ⟨1, one_pow 2, by rw [C_1, one_mul, rename_prodMap_one]⟩
  | swap_mul σ x y _ ih =>
    obtain ⟨c, hc2, hc⟩ := ih
    obtain ⟨d, hd2, hd⟩ := hf.rename_swap x y
    refine ⟨d * c, by rw [mul_pow, hc2, hd2, one_mul], ?_⟩
    rw [rename_prodMap_mul, hc, map_mul, rename_C, hd, C_mul]
    ring
end GroundTheory.Heights₂.Heights
