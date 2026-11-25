-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_KThm_upward_594d791661c9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:32:58.876559+00:00
-- url     : https://prove2.me/submissions/c0daee65-544f-4498-8a61-e128b2f64036

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_GeneratedTwistSysZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PVeryAmpleNefPlusAmple
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_pow_a678e760a862
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_mul_367f4f97d00d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_span_zpow_pow_d59270f20e61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_sub_twistMul_2727aa0a3e72
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twist_944da96fb0e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_pow_f814712537f9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_generated_twistSys_nat_4a88fe4e3490
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_KThm_lbPow_toSubSystem_1a6630de4309
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_isVeryAmple_twistSys_one_40d8ce118432


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
variable {k : Type u} [Field k] {Ω : Type w} [Field Ω] [Algebra k Ω] {N : ℕ} {x : Fin (N + 1) → Ω}
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace KThm
theorem _root_.solution (hJ : GraphClosed.Statement.{u, w}) (M : LineBundle k x) (P : ℕ) (m' : ℤ)
    (hP : 1 ≤ P) (hG : (twistMul M.toSubSystem P m').Generated) (t : ℚ) (ht : (m' : ℚ) < P * t) :
    ∃ (p : ℕ) (m : ℤ), 1 ≤ p ∧ (m : ℚ) = p * t ∧ IsVeryAmple (twistMul M.toSubSystem p m) := by
  have hq : 0 < t.den := t.den_pos
  have hnum : (t.num : ℚ) = t * t.den := (Rat.mul_den_eq_num t).symm
  have hlt : ((t.den : ℤ) * m' : ℤ) < (P : ℤ) * t.num := by
    have h1 : ((t.den : ℚ) * m') < P * t.num := by
      rw [hnum]
      have : (0 : ℚ) < t.den := by exact_mod_cast hq
      nlinarith
    exact_mod_cast h1
  set e : ℤ := P * t.num - t.den * m' - 1 with he_def
  have he : 0 ≤ e := by omega
  let G : LineBundle k x := KThm.lbTwist (KThm.lbPow (KThm.lbTwist (KThm.lbPow M P) (twistBundle k x m')) t.den)
    (twistBundle k x e)
  have hGsub : G.toSubSystem = ((twistMul M.toSubSystem P m').pow t.den).twist (twistSys k x e) := by
    change (KThm.lbPow _ t.den).toSubSystem.twist (twistSys k x e) = _
    rw [KThm.lbPow_toSubSystem]
    change ((((KThm.lbPow M P).toSubSystem).twist (twistSys k x m')).pow t.den).twist _ = _
    rw [KThm.lbPow_toSubSystem]
    rfl
  have hGgen : G.toSubSystem.Generated := by
    rw [hGsub]
    refine KThm.generated_twist (KThm.generated_pow hG _) ?_
    have := KThm.generated_twistSys_nat (S := k) (x := x) e.toNat
    rwa [Int.toNat_of_nonneg he] at this
  have hV := hJ k Ω N x G (twistBundle k x 1) hGgen isVeryAmple_twistSys_one
  refine ⟨P * t.den, P * t.num, Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)),
    by push_cast; rw [hnum]; ring, ?_⟩
  convert hV using 1
  refine SubSystem.ext_sub fun I => ?_
  obtain ⟨i, hi⟩ := I.2.1
  rw [KThm.sub_twistMul _ _ _ I hi, KThm.sub_twist, hGsub, KThm.sub_twist, KThm.sub_pow,
    KThm.sub_twistMul _ _ _ I hi]
  change _ = twistMod k x 1 I * (twistMod k x e I * _)
  rw [twistMod_eq_span _ I hi, twistMod_eq_span _ I hi, mul_pow, ← pow_mul, KThm.span_zpow_pow I hi,
    mul_left_comm (Submodule.span _ {x i ^ e}), mul_left_comm (Submodule.span _ {x i ^ (1 : ℤ)}),
    KThm.span_zpow_mul I hi, KThm.span_zpow_mul I hi]
  congr 3
  rw [he_def]; ring_nf
end KThm
end GroundTheory.Heights₂.Heights.Kleiman
