-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_NefPlusAmple_proof_e40df428f473
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:50:04.440898+00:00
-- url     : https://prove2.me/submissions/fd25820d-8275-4f17-97f5-d1c153aa0ba0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GenericPointSectionHypotheses
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsJoin
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_eq_mul_d7e23ae652ec
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_pow_sub_eq_pow_ebcff08057ae
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_generated_pow_505c8b42e2a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isUnit_twistMod_cc1f7a09138b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_LineBundle_isUnit_sub_15c6f8ce3176
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twist_pow_eq_twistMul_twist_a9905eaca05a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_exists_isSubvar_primeOf_150c48c899b8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_of_eq_zero_44fe3d743ff6

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
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace NefPlusAmple
theorem _root_.solution (hGA : GeneratedAmple.Statement.{u, w})
    (hK : VeryAmpleNefPlusAmple.Statement.{u, w}) (hJ : VeryAmpleTwistGenerated.Statement.{u, w}) :
    NefPlusAmple.Statement.{u, w} := by
  intro k _ Ω _ _ N x M H hH hM ε hε
  by_cases hx : x = 0
  · refine ⟨ε.den, ε.num.toNat, ε.den_pos, ?_, isVeryAmple_of_eq_zero hx _⟩
    rw [Rat.den_mul_eq_num, ← Int.cast_natCast, Int.toNat_of_nonneg (Rat.num_pos.mpr hε).le]
  obtain ⟨d, hd⟩ := exists_isSubvar_primeOf (k := k) hx
  obtain ⟨c₀, hc₀⟩ := hGA k Ω N x H hH (twistBundle k x (-1))
  have hc : 1 ≤ max c₀ 1 := le_max_right _ _
  have hgen := hc₀ (max c₀ 1) (le_max_left _ _)
  have hcq : (0 : ℚ) < (max c₀ 1 : ℕ) := by exact_mod_cast hc
  obtain ⟨q, m, hq, hm, hVA⟩ := hK k d Ω N x M hd hM (ε / (max c₀ 1 : ℕ)) (div_pos hε hcq)
  have hm0 : 0 ≤ m := by
    have : (0 : ℚ) ≤ m := by rw [hm]; positivity
    exact_mod_cast this
  have hmq : ((m.toNat : ℕ) : ℚ) = m := by
    rw [← Int.cast_natCast, Int.toNat_of_nonneg hm0]
  refine ⟨q, max c₀ 1 * m.toNat, hq, ?_, ?_⟩
  · rw [Nat.cast_mul, hmq, hm]
    field_simp
  · rw [twist_pow_eq_twistMul_twist M.toSubSystem H.toSubSystem (twistBundle k x (-1)).toSubSystem
      (fun _ => rfl)]
    refine hJ k Ω N x _ _ (fun I => ?_) (fun I => ?_) ?_ (SubSystem.generated_pow hgen _)
    · refine IsUnit.exists_right_inv ?_
      simp only [twistMul, SubSystem.twist_sub_eq_mul, SubSystem.pow_sub_eq_pow]
      exact ((M.isUnit_sub I).pow q).mul (isUnit_twistMod _ I)
    · refine IsUnit.exists_right_inv ?_
      simp only [SubSystem.twist_sub_eq_mul, SubSystem.pow_sub_eq_pow]
      exact ((isUnit_twistMod (-1) I).mul ((H.isUnit_sub I).pow _)).pow _
    · rwa [Int.toNat_of_nonneg hm0]
end NefPlusAmple
end GroundTheory.Heights₂.Heights.Kleiman
