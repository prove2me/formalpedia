-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_SemiPosTwist_proof_9e1542759b69
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:32:51.033624+00:00
-- url     : https://prove2.me/submissions/a8a5b5a0-766b-41aa-b9a1-f70a11090fa0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NoCommonComponentCoordinatesPlane
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_ArithModel
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovGeometry_ADensStC
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PshShiftA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LeviOneEqLaplacianThm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PSemiPosTwist
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_isOpen_noZeroBlock_a770c8a08c0b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_pos_a55aaaab7fd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_rho_eq_dd540dfc94fd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_contDiffAt_F_f4d4961f9626
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_F_nonneg_3b4ca4329192
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_add_sum_a5029caeb5fa
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_levi_zero_fun_1d97ee7a5fc5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_SemipositiveTwist_laplacian_line_eq_levi_3ac6aef88d61
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isSmoothHerm_sqMetric
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
attribute [local simp] P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508



set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian
open SemipositiveTwist
namespace GroundTheory.Heights₂.Heights.Inter
namespace SemiPosTwist
theorem _root_.solution (hB : TorusInvLevi.Statement) : SemiPosTwist.Statement := by
  intro K _ ι _ M hM
  classical
  have hUo := isOpen_noZeroBlock (ι := ι)
  set u : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (M.h y) + ∑ k, (-(M.a k : ℝ)) * F k y with hu
  have hlogM : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ContDiffAt ℝ 2 (fun y => Real.log (M.h y)) z := fun z hz =>
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos z hz).ne'
  have hu2 : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 u z := fun z hz =>
    (levi_add_sum _ F (fun k => -(M.a k : ℝ)) (hlogM z hz) (contDiffAt_F hz) 0 Finset.univ).1

  have hinv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z := by
    intro c z hc hz
    have hcn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have hF : ∀ k, F k (fun p => c p.1 * z p) = Real.log ‖c k‖ + F k z := by
      intro k
      show Real.log ((fsMetric (ι k)).ρ (c k • fun i => z ⟨k, i⟩)) =
        Real.log ‖c k‖ + Real.log ((fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩))
      rw [(fsMetric (ι k)).smul, Real.log_mul (hcn k) (rho_pos hz k).ne']
    have hh : Real.log (M.h (fun p => c p.1 * z p)) =
        ∑ k, (M.a k : ℝ) * Real.log ‖c k‖ + Real.log (M.h z) := by
      rw [M.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hcn k))
        (M.pos z hz).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hcn k))]
      simp only [Real.log_zpow]
    rw [hu]
    show Real.log (M.h (fun p => c p.1 * z p)) + ∑ k, (-(M.a k : ℝ)) * F k (fun p => c p.1 * z p) =
      Real.log (M.h z) + ∑ k, (-(M.a k : ℝ)) * F k z
    rw [hh]
    simp only [hF, mul_add, Finset.sum_add_distrib, neg_mul, Finset.sum_neg_distrib]
    ring
  obtain ⟨C, hC⟩ := hB K ι u (fun z hz => (hu2 z hz).contDiffWithinAt) hinv

  have hΦ : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ∀ w,
      leviForm (fun y => ∑ k, Real.log ((fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩))) z w =
        ∑ k, ReciprocityTheory.AnForm.levi (F k) z w := by
    intro z hz w
    have h := (levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => 1) contDiffAt_const (contDiffAt_F hz) w
      Finset.univ).2
    simp only [zero_add, one_mul, levi_zero_fun] at h
    exact h

  set N : ℕ := ⌈|C| + ∑ k, |(M.a k : ℝ)|⌉₊ with hN
  have hNk : ∀ k, C ≤ (M.a k : ℝ) + N := by
    intro k
    have h1 : |C| + ∑ k, |(M.a k : ℝ)| ≤ N := Nat.le_ceil _
    have h2 : |(M.a k : ℝ)| ≤ ∑ k, |(M.a k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(M.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 := le_abs_self C
    have h4 := neg_abs_le (M.a k : ℝ)
    linarith
  set T : HermLine ι := HermLine.sqMetric (fun _ => N) with hT
  have hlogT : ∀ y : (Σ k, ι k) → ℂ, (∀ k, ∃ i, y ⟨k, i⟩ ≠ 0) →
      Real.log (T.h y) = ∑ k, (N : ℝ) * F k y := by
    intro y hy
    have h : T.h y = ∏ k, (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) ^ N := by
      simp only [hT, HermLine.sqMetric, rho_eq]
    rw [h, Real.log_prod (fun k _ => pow_ne_zero _ (rho_pos hy k).ne')]
    simp only [Real.log_pow, F]
  refine ⟨T, isSmoothHerm_sqMetric _, ?_, ?_⟩
  · intro z hz v
    have hs := levi_add_sum (fun _ => (0 : ℝ)) F (fun _ => (N : ℝ)) contDiffAt_const (contDiffAt_F hz) v
      Finset.univ
    beta_reduce at hs
    have hev : (fun y => Real.log (T.h y)) =ᶠ[𝓝 z] fun y => 0 + ∑ k, (N : ℝ) * F k y := by
      filter_upwards [hUo.mem_nhds hz] with y hy
      rw [hlogT y hy, zero_add]
    rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v,
      hs.2, levi_zero_fun, zero_add]
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun k _ =>
      mul_nonneg (Nat.cast_nonneg _) (levi_F_nonneg hz k v))
  · intro z hz v
    have hs := levi_add_sum u F (fun k => (M.a k : ℝ) + N) (hu2 z hz) (contDiffAt_F hz) v Finset.univ
    beta_reduce at hs
    have hev : (fun y => Real.log ((M.tensor T).h y)) =ᶠ[𝓝 z]
        fun y => u y + ∑ k, ((M.a k : ℝ) + N) * F k y := by
      filter_upwards [hUo.mem_nhds hz] with y hy
      show Real.log (M.h y * T.h y) = _
      rw [Real.log_mul (M.pos y hy).ne' (T.pos y hy).ne', hlogT y hy, hu]
      simp only [add_mul, neg_mul, Finset.sum_add_distrib, Finset.sum_neg_distrib]
      ring
    rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v, hs.2]
    have hC' : |ReciprocityTheory.AnForm.levi u z v| ≤ C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [← hΦ z hz v]
      exact hC z hz v
    have hsum : 0 ≤ ∑ k, ((M.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hNk k]) (levi_F_nonneg hz k v)
    have hexp : ∑ k, ((M.a k : ℝ) + N) * ReciprocityTheory.AnForm.levi (F k) z v =
        ∑ k, ((M.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v +
          C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h5 := neg_abs_le (ReciprocityTheory.AnForm.levi u z v)
    linarith
end SemiPosTwist
end GroundTheory.Heights₂.Heights.Inter
