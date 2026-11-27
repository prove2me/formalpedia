-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_MollifiedNearSmooth_proof_9513a6a78ec5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:43.625726+00:00
-- url     : https://prove2.me/submissions/4b9d523e-2888-40fb-a392-6f5be255fcb0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StatementsTruncPsh
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PMollifiedNearSmooth
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_exists_q_lower_6333d7d43fa6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_differentiableAt_u_245b9536963d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_near_point_f569195abf0f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_PotentialCharts_mid_subset_source_96b409876f03
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RegChartData_symm_mem_Yo_ad344fcd4555
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_log_inv_facts_1450b9e21f5d
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Metric
open scoped ContDiff
open ReciprocityTheory.AnForm.A (polyMax molli mollify_thm polyMax_le' coordDiv limsupExt)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
namespace MollifiedNearSmooth
theorem _root_.solution (h : TruncPsh.Statement) : MollifiedNearSmooth.Statement := by
  intro X _ _ _ D A R ρ
  obtain ⟨δ, B₀, hδ, hV⟩ := h X D A R
  choose V hVo hVt hVball hVpsh using hV
  obtain ⟨Q, hQ0, hQ⟩ := R.exists_q_lower
  obtain ⟨B, hB⟩ := R.f_bdd
  obtain ⟨B', hB'⟩ : ∃ b : ℝ, b = max B 0 := ⟨_, rfl⟩
  have hB'0 : 0 ≤ B' := hB' ▸ le_max_right _ _
  have hfB : ∀ j, ∀ y ∈ (R.chart j).target, |R.f j y| ≤ B' :=
    fun j y hy => (hB j y hy).trans (hB' ▸ le_max_left _ _)
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 2 * B' + D * Real.log 4 := ⟨_, rfl⟩
  have hc0 : 0 ≤ c := hc ▸ add_nonneg (by linarith)
    (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by norm_num)))
  obtain ⟨G, hG⟩ : ∃ g : ℝ, g = |R.Cgrad| := ⟨_, rfl⟩
  have hG0 : 0 ≤ G := hG ▸ abs_nonneg _
  obtain ⟨Cl, hCl⟩ : ∃ g : ℝ, g = |R.Clog| := ⟨_, rfl⟩
  have hCl0 : 0 ≤ Cl := hCl ▸ abs_nonneg _
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = max (G * 2 ^ G * Real.exp (c / 2)) (max G (Q + Cl)) := ⟨_, rfl⟩
  have hC1 : G * 2 ^ G * Real.exp (c / 2) ≤ C := hC ▸ le_max_left _ _
  have hC2 : G ≤ C := hC ▸ (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Q + Cl ≤ C := hC ▸ (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, min (min δ (Real.exp (-B') / 4)) (Real.exp (-(Real.exp 1 + 2 * c))),
    lt_min (lt_min hδ (by positivity)) (Real.exp_pos _), ?_⟩
  intro t ht ht₀ K hK j x hx hrx
  simp only [lt_min_iff] at ht₀
  obtain ⟨⟨htδ, htB⟩, hte⟩ := ht₀
  obtain ⟨hℓc, hlogℓ⟩ := log_inv_facts ht hc0 hte
  have he1 : 1 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hℓ1 : 1 ≤ Real.log t⁻¹ := by linarith
  have hxs : x ∈ (R.chart j).source := R.mid_subset_source j hx.1
  have hballV : closedBall (R.chart j x) t ⊆ V j :=
    (closedBall_subset_closedBall htδ.le).trans (hVball j x hx.1)
  have hballT : closedBall (R.chart j x) t ⊆ (R.chart j).target := hballV.trans (hVt j)
  have hnear := fun y (hy : y ∈ closedBall (R.chart j x) t) =>
    R.near_point ht hfB htB.le hx.1 hx.2 hrx hy (hballT hy)
  rw [← hc] at hnear

  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = G * (Real.log t⁻¹ + c) ^ G * Real.exp ((Real.log t⁻¹ + c) / 2) :=
    ⟨_, rfl⟩
  have hM0 : 0 ≤ M := hM ▸ by positivity
  have hgrad : ∀ y ∈ closedBall (R.chart j x) t, ‖fderiv ℝ (R.u j) y‖ ≤ M := by
    intro y hy
    obtain ⟨hyA, hry⟩ := hnear y hy
    have hyT := hballT hy
    have h1r : 1 ≤ R.r ((R.chart j).symm y) := R.one_le_r _ (R.symm_mem_Yo j hyT hyA)
    have hg := R.grad_le j y ⟨hyT, hyA⟩
    have e1 : R.Cgrad * R.r ((R.chart j).symm y) ^ R.Cgrad ≤ G * R.r ((R.chart j).symm y) ^ G :=
      (mul_le_mul_of_nonneg_right (hG ▸ le_abs_self _) (by positivity)).trans
        (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le h1r (hG ▸ le_abs_self _)) hG0)
    have e2 : R.r ((R.chart j).symm y) ^ G ≤ (Real.log t⁻¹ + c) ^ G :=
      Real.rpow_le_rpow (by linarith) hry hG0
    have e3 : Real.exp (R.r ((R.chart j).symm y) / 2) ≤ Real.exp ((Real.log t⁻¹ + c) / 2) :=
      Real.exp_le_exp.2 (by linarith)
    refine hg.trans ?_
    rw [hM]
    calc R.Cgrad * R.r ((R.chart j).symm y) ^ R.Cgrad * Real.exp (R.r ((R.chart j).symm y) / 2)
        ≤ G * R.r ((R.chart j).symm y) ^ G * Real.exp (R.r ((R.chart j).symm y) / 2) :=
          mul_le_mul_of_nonneg_right e1 (Real.exp_pos _).le
      _ ≤ G * (Real.log t⁻¹ + c) ^ G * Real.exp ((Real.log t⁻¹ + c) / 2) :=
          mul_le_mul (mul_le_mul_of_nonneg_left e2 hG0) e3 (Real.exp_pos _).le (by positivity)

  have hmv : ∀ y ∈ closedBall (R.chart j x) t, R.u j y ≤ R.u j (R.chart j x) + M * t := by
    intro y hy
    have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun y' hy' => R.differentiableAt_u j (hballT hy') (hnear y' hy').1) hgrad
      (convex_closedBall _ t) (mem_closedBall_self ht.le) hy
    have h2 : ‖y - R.chart j x‖ ≤ t := by rw [← dist_eq_norm]; exact mem_closedBall.1 hy
    have h3 := le_abs_self (R.u j y - R.u j (R.chart j x))
    rw [← Real.norm_eq_abs] at h3
    nlinarith [mul_le_mul_of_nonneg_left h2 hM0]

  have huz : -K ≤ R.u j (R.chart j x) := by
    have hu : R.u j (R.chart j x) = R.q j (R.chart j x) + R.ph x := by
      show R.q j (R.chart j x) + R.ph ((R.chart j).symm (R.chart j x)) = _
      rw [(R.chart j).left_inv hxs]
    have hr1 : 1 ≤ R.r x := R.one_le_r x hx.2
    have hL0 : 0 ≤ Real.log (R.r x) := Real.log_nonneg hr1
    have hL : Real.log (R.r x) ≤ Real.log (Real.log t⁻¹) := Real.log_le_log (by linarith) hrx
    have hph := R.ph_ge x hx.2
    have e1 : R.Clog * Real.log (R.r x) ≤ Cl * Real.log (Real.log t⁻¹) :=
      (mul_le_mul_of_nonneg_right (hCl ▸ le_abs_self _) hL0).trans (mul_le_mul_of_nonneg_left hL hCl0)
    have e2 : Q ≤ Q * Real.log (Real.log t⁻¹) := le_mul_of_one_le_right hQ0 hlogℓ.le
    have e3 : (Q + Cl) * Real.log (Real.log t⁻¹) ≤ C * Real.log (Real.log t⁻¹) :=
      mul_le_mul_of_nonneg_right hC3 (by linarith)
    have e4 := hQ j x hx.1
    have e5 : -R.Clog * Real.log (R.r x) = -(R.Clog * Real.log (R.r x)) := by ring
    have e6 : (Q + Cl) * Real.log (Real.log t⁻¹) =
        Q * Real.log (Real.log t⁻¹) + Cl * Real.log (Real.log t⁻¹) := by ring
    linarith

  have hbound : M * t ≤ C * Real.log t⁻¹ ^ C * t ^ (1 / 2 : ℝ) := by
    have ht' : Real.exp (Real.log t⁻¹ / 2) * t = t ^ (1 / 2 : ℝ) := by
      rw [Real.rpow_def_of_pos ht, Real.log_inv]
      calc Real.exp (-Real.log t / 2) * t = Real.exp (-Real.log t / 2) * Real.exp (Real.log t) := by
            rw [Real.exp_log ht]
        _ = Real.exp (Real.log t * (1 / 2)) := by
            rw [← Real.exp_add]
            congr 1
            ring
    have hMt : M * t = G * (Real.log t⁻¹ + c) ^ G * Real.exp (c / 2) * t ^ (1 / 2 : ℝ) := by
      rw [hM, ← ht', show (Real.log t⁻¹ + c) / 2 = Real.log t⁻¹ / 2 + c / 2 by ring, Real.exp_add]
      ring
    have e4 : (Real.log t⁻¹ + c) ^ G ≤ 2 ^ G * Real.log t⁻¹ ^ G := by
      rw [← Real.mul_rpow (by norm_num) (by linarith)]
      exact Real.rpow_le_rpow (by linarith) (by linarith) hG0
    have e5 : Real.log t⁻¹ ^ G ≤ Real.log t⁻¹ ^ C := Real.rpow_le_rpow_of_exponent_le hℓ1 hC2
    have hs : 0 ≤ t ^ (1 / 2 : ℝ) := by positivity
    rw [hMt]
    calc G * (Real.log t⁻¹ + c) ^ G * Real.exp (c / 2) * t ^ (1 / 2 : ℝ)
        ≤ G * (2 ^ G * Real.log t⁻¹ ^ G) * Real.exp (c / 2) * t ^ (1 / 2 : ℝ) := by gcongr
      _ = G * 2 ^ G * Real.exp (c / 2) * Real.log t⁻¹ ^ G * t ^ (1 / 2 : ℝ) := by ring
      _ ≤ C * Real.log t⁻¹ ^ C * t ^ (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul hC1 e5 (by positivity) (by linarith)) hs

  have hi : molli ρ t (R.trunc K j) (R.chart j x) ≤ polyMax (R.trunc K j) (R.chart j x) t :=
    (((mollify_thm D ρ (V j) (R.trunc K j) (hVo j) (hVpsh j K).1).1 t ht).2.2.2
      (R.chart j x) hballV).2
  have hii : polyMax (R.trunc K j) (R.chart j x) t ≤ R.u j (R.chart j x) + M * t :=
    polyMax_le' ht.le fun y hy => by
      have hyA := (hnear y hy).1
      simp only [RegChartData.trunc, limsupExt, if_neg hyA]
      exact max_le (hmv y hy) (by nlinarith)
  simp only [RegChartData.smoothed]
  linarith
end MollifiedNearSmooth
end GroundTheory.Heights₂.Heights.Regular
