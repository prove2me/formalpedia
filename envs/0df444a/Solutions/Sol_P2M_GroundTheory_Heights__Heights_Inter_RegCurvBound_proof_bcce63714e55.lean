-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_RegCurvBound_proof_bcce63714e55
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T05:01:36.673555+00:00
-- url     : https://prove2.me/submissions/502013e2-f9a6-45f2-84d8-563ce01c8878

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StRegCurvBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StTorusInvLevi
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_RegularizedCurvature
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PRegCurvBound
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_one_661faae583ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_ProjLine_y_zero_4f3b615e7508
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_analyticAt_eval_map_1ab986667e3b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_contDiffAt_F_02c255d304b9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_isOpen_noZeroBlock_3cc95b89e6b5
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_laplacian_line_eq_levi_a835370ca665
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_F_nonneg_d0a17bf941a0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_add_sum_d4ff2f3317d8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_const_1f6796170df7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_levi_logSum_9d1d85a5a3b6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_RegularizedCurvature_rho_pos_fa482035c771
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_isSmoothHerm_regLine_8cd27babf8cd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Inter_log_regLine_h_743c8a7df0e2
import Theorems.Thm_ReciprocityTheory_AnForm_levi_congr
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
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology InnerProductSpace Laplacian RegularizedCurvature MvPolynomial
namespace GroundTheory.Heights₂.Heights.Inter
namespace RegCurvBound
theorem _root_.solution (hB : TorusInvLevi.Statement) : RegCurvBound.Statement := by
  intro K _ ι _ E t ht hE
  classical
  have hUo := isOpen_noZeroBlock (ι := ι)
  have hlogH : ∀ M : HermLine ι, IsSmoothHerm M → ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      ContDiffAt ℝ 2 (fun y => Real.log (M.h y)) z := fun M hM z hz =>
    ((hM.contDiffAt (hUo.mem_nhds hz)).of_le (WithTop.coe_le_coe.2 le_top)).log (M.pos z hz).ne'
  set u : ((Σ k, ι k) → ℂ) → ℝ := fun y => Real.log (E.h y) + ∑ k, (-(E.a k : ℝ)) * F k y with hu
  have hu2 : ∀ z : (Σ k, ι k) → ℂ, (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) → ContDiffAt ℝ 2 u z := fun z hz =>
    (levi_add_sum _ F (fun k => -(E.a k : ℝ)) (hlogH E hE z hz) (contDiffAt_F hz) 0 Finset.univ).1

  have hinv : ∀ (c : K → ℂ) (z : (Σ k, ι k) → ℂ), (∀ k, c k ≠ 0) → (∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) →
      u (fun p => c p.1 * z p) = u z := by
    intro c z hc hz
    have hcn : ∀ k, ‖c k‖ ≠ 0 := fun k => norm_ne_zero_iff.mpr (hc k)
    have hF : ∀ k, F k (fun p => c p.1 * z p) = Real.log ‖c k‖ + F k z := by
      intro k
      show Real.log ((fsMetric (ι k)).ρ (c k • fun i => z ⟨k, i⟩)) =
        Real.log ‖c k‖ + Real.log ((fsMetric (ι k)).ρ (fun i => z ⟨k, i⟩))
      rw [(fsMetric (ι k)).smul, Real.log_mul (hcn k) (rho_pos hz k).ne']
    have hh : Real.log (E.h (fun p => c p.1 * z p)) =
        ∑ k, (E.a k : ℝ) * Real.log ‖c k‖ + Real.log (E.h z) := by
      rw [E.smul c z hc, Real.log_mul (Finset.prod_ne_zero_iff.mpr fun k _ => zpow_ne_zero _ (hcn k))
        (E.pos z hz).ne', Real.log_prod (fun k _ => zpow_ne_zero _ (hcn k))]
      simp only [Real.log_zpow]
    rw [hu]
    show Real.log (E.h (fun p => c p.1 * z p)) + ∑ k, (-(E.a k : ℝ)) * F k (fun p => c p.1 * z p) =
      Real.log (E.h z) + ∑ k, (-(E.a k : ℝ)) * F k z
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
    simp only [zero_add, one_mul, levi_const] at h
    exact h

  set N : ℕ := ⌈|C| + ∑ k, |(E.a k : ℝ)|⌉₊ with hN
  have hNk : ∀ k, C ≤ (E.a k : ℝ) + N := by
    intro k
    have h1 : |C| + ∑ k, |(E.a k : ℝ)| ≤ N := Nat.le_ceil _
    have h2 : |(E.a k : ℝ)| ≤ ∑ k, |(E.a k : ℝ)| :=
      Finset.single_le_sum (f := fun k => |(E.a k : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ k)
    have h3 := le_abs_self C
    have h4 := neg_abs_le (E.a k : ℝ)
    linarith
  refine ⟨N, fun ε hε => ?_⟩
  set R : HermLine ι := regLine E t ht ε with hR
  have hRs : IsSmoothHerm R := isSmoothHerm_regLine hE hε
  intro z hz v
  have hW0 : 0 ≤ ∑ k, ReciprocityTheory.AnForm.levi (F k) z v :=
    Finset.sum_nonneg fun k _ => levi_F_nonneg hz k v

  have hLW : 0 ≤ ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    have hs := levi_add_sum u F (fun k => (E.a k : ℝ)) (hu2 z hz) (contDiffAt_F hz) v Finset.univ
    have hfun : (fun y => u y + ∑ k, (E.a k : ℝ) * F k y) = fun y => Real.log (E.h y) := by
      funext y
      simp only [hu, neg_mul, Finset.sum_neg_distrib]
      ring
    rw [hfun] at hs
    have hC' : |ReciprocityTheory.AnForm.levi u z v| ≤ C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [← hΦ z hz v]
      exact hC z hz v
    have hsum : 0 ≤ ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v :=
      Finset.sum_nonneg fun k _ => mul_nonneg (by linarith [hNk k]) (levi_F_nonneg hz k v)
    have hexp : ∑ k, (E.a k : ℝ) * ReciprocityTheory.AnForm.levi (F k) z v + N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v =
        ∑ k, ((E.a k : ℝ) + N - C) * ReciprocityTheory.AnForm.levi (F k) z v +
          C * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring
    have h5 := neg_abs_le (ReciprocityTheory.AnForm.levi u z v)
    rw [hs.2]
    linarith

  have hΦ1 : ContDiffAt ℝ 2 (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) z :=
    (hlogH E hE z hz).add (contDiffAt_const.mul (hlogH R hRs z hz))
  obtain ⟨μ, hμ0, hμ1, hμ⟩ := levi_logSum (h := E.h)
    (T := fun y => eval y (map (Int.castRingHom ℂ) t))
    (Φ := fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) (hlogH E hE z hz)
    (by filter_upwards [hUo.mem_nhds hz] with y hy; exact E.pos y hy) (analyticAt_eval_map t z) hε hΦ1
    (fun y => by rw [hR, log_regLine_h, secNorm, one_mul]) v

  have hs := levi_add_sum (fun y => Real.log (E.h y) + 1 * Real.log (R.h y)) F (fun _ => (N : ℝ)) hΦ1
    (contDiffAt_F hz) v Finset.univ
  have hev : (fun y => Real.log (((E.tensor R).tensor
      (HermLine.ofMetrics (fun k => fsMetric (ι k)) (fun _ => (N : ℤ)))).h y)) =ᶠ[𝓝 z]
      fun y => (Real.log (E.h y) + 1 * Real.log (R.h y)) + ∑ k, (N : ℝ) * F k y := by
    filter_upwards [hUo.mem_nhds hz] with y hy
    show Real.log ((E.h y * R.h y) * ∏ k, (fsMetric (ι k)).ρ (fun i => y ⟨k, i⟩) ^ ((N : ℤ))) = _
    rw [Real.log_mul (mul_pos (E.pos y hy) (R.pos y hy)).ne'
        (Finset.prod_pos fun k _ => zpow_pos (rho_pos hy k) _).ne',
      Real.log_mul (E.pos y hy).ne' (R.pos y hy).ne',
      Real.log_prod (fun k _ => (zpow_pos (rho_pos hy k) _).ne')]
    simp only [Real.log_zpow, F, Int.cast_natCast, one_mul]
  rw [laplacian_line_eq_levi (hs.1.congr_of_eventuallyEq hev) v, ReciprocityTheory.AnForm.levi_congr hev v, hs.2,
    ← Finset.mul_sum]
  have hmu : 0 ≤ μ * ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v +
      N * ∑ k, ReciprocityTheory.AnForm.levi (F k) z v := by
    rcases le_or_gt 0 (ReciprocityTheory.AnForm.levi (fun y => Real.log (E.h y)) z v) with hL0 | hL0
    · exact add_nonneg (mul_nonneg hμ0 hL0) (mul_nonneg (Nat.cast_nonneg _) hW0)
    · nlinarith
  linarith
end RegCurvBound
end GroundTheory.Heights₂.Heights.Inter
