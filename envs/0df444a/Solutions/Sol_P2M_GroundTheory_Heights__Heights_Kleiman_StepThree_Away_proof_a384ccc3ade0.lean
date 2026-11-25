-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_proof_a384ccc3ade0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:51:53.400174+00:00
-- url     : https://prove2.me/submissions/3a87dfe7-21ac-4b4f-9d49-9d938f34440c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepThreeAway
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PStepThreeAway
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_span_singleton_pow_eq_8da0cdeb9c32
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistSys_sub_75e697ae4511
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twist_sub_46528efab20e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_mul_67d3a62e5b05
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_twistMod_pow_475c988a681c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_pow_sub_af11ca77aee4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_StepThree_Away_idealMod_zeroIdeal_mul_le_be5ef0c4f392

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
open GroundTheory.Heights₂.Heights.Kleiman.StepThree GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
namespace GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
theorem _root_.solution : StepThree.Away.Statement.{u, w} := by
  intro k _ Ω _ _ N x T b c hc I
  obtain ⟨i, hi⟩ := I.2.1
  have hL : ∀ I' : Chart x, T.L.sub I' = twistMod k x T.c₁ I' * T.D.sub I' := by
    intro I'
    change ((T.M.toSubSystem.pow T.p).twist (twistSys k x T.m)).sub I' =
      _ * ((T.M.toSubSystem.pow T.p).twist (twistSys k x (T.m - T.c₁))).sub I'
    rw [twist_sub, twist_sub, twistSys_sub, twistSys_sub, ← mul_assoc, twistMod_mul,
      add_sub_cancel]
  have hF : ∀ I' : Chart x, ((T.L.pow b).twist (twistSys k x c)).sub I' =
      twistMod k x (c + b * T.c₁) I' * T.D.sub I' ^ b := by
    intro I'
    rw [twist_sub, twistSys_sub, pow_sub, hL, mul_pow, twistMod_pow, ← mul_assoc, twistMod_mul]
  have hn : 0 ≤ c + b * T.c₁ :=
    add_nonneg hc (mul_nonneg (Nat.cast_nonneg b) (by linarith [T.c₁_pos]))
  obtain ⟨n, hnn⟩ := Int.eq_ofNat_of_zero_le hn

  have hy : x i ^ n * T.si ^ b ∈ ((T.L.pow b).twist (twistSys k x c)).secs := by
    refine (Submodule.mem_iInf _).mpr fun I' => ?_
    change _ ∈ ((T.L.pow b).twist (twistSys k x c)).sub I'
    rw [hF I', hnn]
    refine Submodule.mul_mem_mul (Submodule.subset_span ⟨X i ^ n, 1, 0, n, one_mem _,
      isHomogeneous_X_pow i n, isHomogeneous_one _ _, by simp, by simp⟩)
      (Submodule.pow_mem_pow _ ?_ b)
    exact (Submodule.mem_iInf _).mp T.si_mem I'

  have hbound : idealMod (x := x) T.J I ^ b * ((T.L.pow b).twist (twistSys k x c)).sub I ≤
      Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by
    rw [hF I, mul_left_comm, ← mul_pow]
    calc twistMod k x (c + b * T.c₁) I * (idealMod (x := x) T.J I * T.D.sub I) ^ b
        ≤ twistMod k x (c + b * T.c₁) I * Submodule.span (chartRing k x I) {T.si} ^ b := by
          gcongr
          exact idealMod_zeroIdeal_mul_le T.D T.si I
      _ = Submodule.span (chartRing k x I) {x i ^ n * T.si ^ b} := by
          rw [twistMod_eq_span _ I hi, span_singleton_pow_eq, Submodule.span_mul_span,
            Set.singleton_mul_singleton, hnn, zpow_natCast]
  rw [Submodule.smul_le]
  intro r hr z hz
  have hr' : (r : Ω) ∈ idealMod (x := x) T.J I ^ b := by
    have hm := Submodule.mem_map_of_mem (f := (Algebra.ofId (chartRing k x I) Ω).toLinearMap) hr
    rw [Submodule.map_pow] at hm
    have hle : Submodule.map (Algebra.ofId (chartRing k x I) Ω).toLinearMap
        ((idealMod (x := x) T.J I).comap (Algebra.linearMap (chartRing k x I) Ω)) ≤
          idealMod (x := x) T.J I := by
      rintro y ⟨a, ha, rfl⟩
      exact ha
    exact pow_le_pow_left' hle b hm
  have hrz := hbound (Submodule.mul_mem_mul hr' hz)
  rw [chartRing_smul_def]
  exact Submodule.span_mono (Set.singleton_subset_iff.mpr hy) hrz
end GroundTheory.Heights₂.Heights.Kleiman.StepThree.Away
