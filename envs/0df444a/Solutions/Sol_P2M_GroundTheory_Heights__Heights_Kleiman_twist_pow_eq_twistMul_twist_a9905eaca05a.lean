-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_twist_pow_eq_twistMul_twist_a9905eaca05a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T08:31:09.574004+00:00
-- url     : https://prove2.me/submissions/b2b52a81-8367-4a86-ad86-fe2a79bc0025

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_zero_eq_one_5ef25f86ec85
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_mul_twistMod_032661586f67
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMod_pow_eq_13112438b8ce
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
open MvPolynomial
noncomputable section
universe u w
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ}
  {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
theorem _root_.solution (M H T : SubSystem k x Ω)
    (hT : ∀ I, T.sub I = twistMod k x (-1) I) (q c m : ℕ) :
    (M.pow q).twist (H.pow (c * m)) =
      (twistMul M q (m : ℤ)).twist ((T.twist (H.pow c)).pow m) := by
  refine SubSystem.ext_sub fun I => ?_
  simp only [twistMul, SubSystem.twist_sub_eq_mul, SubSystem.pow_sub_eq_pow, hT]
  change _ = _ * twistMod k x (m : ℤ) I * _
  have key : twistMod k x (m : ℤ) I * twistMod k x (-1) I ^ m = 1 := by
    rw [twistMod_pow_eq, twistMod_mul_twistMod, mul_neg_one, add_neg_cancel, twistMod_zero_eq_one]
  calc M.sub I ^ q * H.sub I ^ (c * m)
      = M.sub I ^ q * H.sub I ^ (c * m) * (twistMod k x (m : ℤ) I * twistMod k x (-1) I ^ m) := by
        rw [key, mul_one]
    _ = _ := by ring
end GroundTheory.Heights₂.Heights.Kleiman
