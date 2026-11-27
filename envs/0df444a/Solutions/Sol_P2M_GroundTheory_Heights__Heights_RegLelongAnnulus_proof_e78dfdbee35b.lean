-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_proof_e78dfdbee35b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:08:00.662209+00:00
-- url     : https://prove2.me/submissions/daa42386-2fed-4d8c-b77e-98ab7d933b32

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StRegRadialWeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StChartMassCompact
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PSheetSumMeasurable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteProjectionCluster
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRegLelongAnnulus
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_congr_fun_99c26fd7616a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_sub__8394cead3316
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_chartDens_const_mul_2440ea3a0ba2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_integrable_chartDens_b4865e99a51f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_integral_chartDens_4b0362defe49
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_radialTransform_f4a0f779ce07
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_hk_of_one_le_ce02361cae31
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_radialTransform_hk_le_c61936e6e318
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_distSq_a3573fb20031
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_distSq_nonneg_983e714bd225
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_mem_euclBall_iff_sq_96ae1db3f54f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_measurableSet_euclBall_b78b99940d0d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_continuous_majorant_0dd58dc25c76
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_hasCompactSupport_majorant_a1a537fd70d7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_le_majorant_a8fad3226038
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_logDistSmooth_44f279e79d7f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_logDistSmooth_eventuallyEq_9826a6050e70
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_hk_indicator_a5a1bc6852e4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_contDiff_annWeight_e989979f7f15
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_zero_of_le_8acb87258ad7
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_annWeight_const_bf676f231701
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_abs_annWeight_le_408cf7b69dc2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_annWeight_0f107cf80e01
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_le_d2a53db5a632
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_radialTransform_diff_of_ge_391b6e41a911
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RegLelongAnnulus_tendsto_radialTransform_diff_5c78029be736
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_smoothNear_of_contDiff_4853c0abca34
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_euclPot_53e03a97724f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_logReg_5c8a3bcec6de
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_smoothNear_of_contDiff_8ca53b5543f3


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
open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff
noncomputable section
open RegLelongAnnulus
namespace GroundTheory.Heights₂.Heights
namespace RegLelongAnnulus
theorem _root_.solution (hRW : RegRadialWeight.Statement) (hCM : ChartMassCompact.Statement) :
    RegLelongAnnulus.Statement := by
  intro n d J A u ε x r s hJ hdim hAf hε hr hrs
  have hs : 0 < s := hr.trans_le hrs
  have hr2 : 0 < r ^ 2 := pow_pos hr 2
  have hs2 : r ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hr.le hrs 2
  have hφσ : ∀ k, SmoothNear (zeroSet J)
      ((vecCons (logReg u ε) fun _ => euclPot : Fin (d + 1) → (Fin n → ℂ) → ℝ) k) := by
    intro k
    refine Fin.cases ?_ (fun i => ?_) k
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
    · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_euclPot n)
  have hball : ∀ ρ, 0 < ρ → ρ ≤ s → Integrable (chartDens J A ((euclBall x ρ).indicator fun _ => (1 : ℝ))
      (vecCons (logReg u ε) fun _ => euclPot)) := by
    intro ρ hρ hρs
    refine integrable_chartDens hCM hJ hdim hAf hφσ (continuous_majorant x s) (hasCompactSupport_majorant x s)
      zero_le_one (measurable_const.indicator (measurableSet_euclBall x ρ))
      (abs_le_majorant x zero_le_one (fun z => ?_) (fun z hz => ?_))
    · by_cases h : z ∈ euclBall x ρ <;> simp [h]
    · refine Set.indicator_of_notMem (fun h => ?_) _
      have h1 := (mem_euclBall_iff_sq x hρ z).1 h
      have h2 : ρ ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hρ.le hρs 2
      linarith
  rcases d with _ | e
  ·
    have hφ : (fun _ : Fin 0 => logDistSq x) = fun _ => euclPot := Subsingleton.elim _ _
    rw [hφ]
    have hsub : ((euclBall x s \ euclBall x r).indicator fun _ => (1 : ℝ)) = fun z =>
        1 * (euclBall x s).indicator (fun _ => (1 : ℝ)) z - 1 * (euclBall x r).indicator (fun _ => (1 : ℝ)) z := by
      funext z
      by_cases h1 : z ∈ euclBall x r
      · have h2 : z ∈ euclBall x s :=
          (mem_euclBall_iff_sq x hs z).2 (((mem_euclBall_iff_sq x hr z).1 h1).trans_le hs2)
        simp [h1, h2]
      · by_cases h2 : z ∈ euclBall x s <;> simp [h1, h2]
    rw [hsub]
    simp only [chartDens_sub' hAf]
    rw [integral_sub ((hball s hs le_rfl).const_mul 1) ((hball r hr hrs).const_mul 1), integral_const_mul,
      integral_const_mul]
    simp
  · have hc0 : 0 ≤ r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) := mul_nonneg (pow_nonneg hr.le _) (pow_nonneg hs.le _)

    have hEq : ∀ k, ∫ y, chartDens J A (fun z => annWeight r s e k (euclPot (z - x)))
          (vecCons (logReg u ε) fun _ => euclPot) y =
        ∫ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
            (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
              radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y := by
      intro k
      have hT : (∫ τ in (0 : ℝ)..s ^ 2, annWeight r s e k τ * (((e + 1 : ℕ) : ℝ) * τ ^ (e + 1 - 1))) = 0 := by
        have h := radialTransform_annWeight e hr hs k (s ^ 2)
        rw [div_self (pow_pos hs 2).ne', radialTransform_hk_of_one_le e k le_rfl,
          radialTransform_hk_of_one_le e k ((one_le_div hr2).2 hs2), sub_self, mul_zero] at h
        unfold radialTransform at h
        rw [annWeight_zero_of_le e hr hrs k le_rfl, zero_mul, zero_sub, neg_eq_zero] at h
        exact h
      have h := hRW n (e + 1) J A u ε x (annWeight r s e k) (pk k * r ^ 2) (s ^ 2) hJ hdim hAf hε
        (contDiff_annWeight e k) (mul_pos (pk_pos k) hr2) (fun t ht => annWeight_const e hr hrs k ht)
        (fun t ht => annWeight_zero_of_le e hr hrs k ht) hT
      have hw : (fun z => radialTransform (e + 1) (annWeight r s e k) (euclPot (z - x))) = fun z =>
          r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) * (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)) :=
        funext fun z => radialTransform_annWeight e hr hs k _
      rw [h, hw]

    have hL : Tendsto (fun k => ∫ y, chartDens J A (fun z => annWeight r s e k (euclPot (z - x)))
          (vecCons (logReg u ε) fun _ => euclPot) y) atTop
        (𝓝 (r ^ (2 * (e + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y) -
          s ^ (2 * (e + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y)) := by
      have h := tendsto_integral_chartDens hCM hJ hdim hAf hφσ (continuous_majorant x s)
        (hasCompactSupport_majorant x s) (C := r ^ (2 * (e + 1)) + s ^ (2 * (e + 1)))
        (add_nonneg (pow_nonneg hr.le _) (pow_nonneg hs.le _))
        (w := fun k z => annWeight r s e k (euclPot (z - x)))
        (w' := fun z => r ^ (2 * (e + 1)) * (euclBall x s).indicator (fun _ => (1 : ℝ)) z -
          s ^ (2 * (e + 1)) * (euclBall x r).indicator (fun _ => (1 : ℝ)) z)
        (fun k => ((contDiff_annWeight e k).continuous.comp (continuous_distSq x)).measurable)
        (fun k => abs_le_majorant x (add_nonneg (pow_nonneg hr.le _) (pow_nonneg hs.le _))
          (fun z => abs_annWeight_le e hr hs k _) (fun z hz => annWeight_zero_of_le e hr hrs k hz))
        (fun z => ((tendsto_hk_indicator x hs z).const_mul _).sub ((tendsto_hk_indicator x hr z).const_mul _))
      have hlim : ∫ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * (euclBall x s).indicator (fun _ => (1 : ℝ)) z -
            s ^ (2 * (e + 1)) * (euclBall x r).indicator (fun _ => (1 : ℝ)) z)
            (vecCons (logReg u ε) fun _ => euclPot) y =
          r ^ (2 * (e + 1)) * (∫ y, chartDens J A ((euclBall x s).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y) -
          s ^ (2 * (e + 1)) * ∫ y, chartDens J A ((euclBall x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => euclPot) y := by
        simp only [chartDens_sub' hAf]
        rw [integral_sub ((hball s hs le_rfl).const_mul _) ((hball r hr hrs).const_mul _), integral_const_mul,
          integral_const_mul]
      rw [← hlim]
      exact h

    have hφτ : ∀ k, SmoothNear (zeroSet J)
        ((vecCons (logReg u ε) fun _ => logDistSmooth x hr : Fin (e + 1 + 1) → (Fin n → ℂ) → ℝ) k) := by
      intro k
      refine Fin.cases ?_ (fun i => ?_) k
      · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logReg u hε)
      · simpa using smoothNear_of_contDiff (S := zeroSet J) (contDiff_logDistSmooth x hr)
    have hgerm : ∀ z : Fin n → ℂ, r ^ 2 / 4 < euclPot (z - x) → ∀ i : Fin (e + 1 + 1),
        (vecCons (logReg u ε) fun _ => logDistSq x : Fin (e + 1 + 1) → (Fin n → ℂ) → ℝ) i =ᶠ[𝓝 z]
          (vecCons (logReg u ε) fun _ => logDistSmooth x hr : Fin (e + 1 + 1) → (Fin n → ℂ) → ℝ) i := by
      intro z hz i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Matrix.cons_val_zero]
        exact Filter.EventuallyEq.rfl
      · simp only [Matrix.cons_val_succ]
        exact (logDistSmooth_eventuallyEq x hr hz).symm
    have hloc : ∀ k y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y =
        chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
          (vecCons (logReg u ε) fun _ => logDistSmooth x hr) y := by
      intro k y
      refine chartDens_congr_fun (fun z _ hz => hgerm z ?_) y
      by_contra hle
      replace hle := not_lt.1 hle
      apply hz
      have hp := half_le_pk k
      rw [radialTransform_diff_of_le e hr hrs k (distSq_nonneg x z) (by nlinarith), mul_zero]
    have hloc' : ∀ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
          (vecCons (logReg u ε) fun _ => logDistSq x) y =
        chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
          (vecCons (logReg u ε) fun _ => logDistSmooth x hr) y := by
      intro y
      refine chartDens_congr_fun (fun z _ hz => hgerm z ?_) y
      by_contra hle
      replace hle := not_lt.1 hle
      apply hz
      rw [Set.indicator_of_notMem (fun h => h.2 ((mem_euclBall_iff_sq x hr z).2 (by linarith))), mul_zero]
    have hR : Tendsto (fun k => ∫ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
          (vecCons (logReg u ε) fun _ => logDistSq x) y) atTop
        (𝓝 (r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          ∫ y, chartDens J A ((euclBall x s \ euclBall x r).indicator fun _ => 1)
            (vecCons (logReg u ε) fun _ => logDistSq x) y)) := by
      have h := tendsto_integral_chartDens hCM hJ hdim hAf hφτ (continuous_majorant x s)
        (hasCompactSupport_majorant x s) (C := 2 * (r ^ (2 * (e + 1)) * s ^ (2 * (e + 1))))
        (by positivity)
        (w := fun k z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2) -
            radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2)))
        (w' := fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
          (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
        (fun k => (continuous_const.mul
          (((continuous_radialTransform e (hk k).continuous).comp ((continuous_distSq x).div_const _)).sub
            ((continuous_radialTransform e (hk k).continuous).comp
              ((continuous_distSq x).div_const _)))).measurable)
        (fun k => abs_le_majorant x (by positivity) (fun z => ?_)
          (fun z hz => by rw [radialTransform_diff_of_ge e hr hrs k hz, mul_zero]))
        (fun z => (tendsto_radialTransform_diff e x hr hrs z).const_mul _)
      · have hl : ∀ y, chartDens J A (fun z => r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) *
              (euclBall x s \ euclBall x r).indicator (fun _ => (1 : ℝ)) z)
              (vecCons (logReg u ε) fun _ => logDistSq x) y =
            r ^ (2 * (e + 1)) * s ^ (2 * (e + 1)) * chartDens J A
              ((euclBall x s \ euclBall x r).indicator fun _ => 1) (vecCons (logReg u ε) fun _ => logDistSq x) y :=
          fun y => chartDens_const_mul hAf _ _ _ y
        rw [← integral_const_mul]
        simp only [← hl, hloc', hloc]
        exact h
      · have h1 := abs_radialTransform_hk_le e k (div_nonneg (distSq_nonneg x z) (pow_pos hs 2).le)
        have h2 := abs_radialTransform_hk_le e k (div_nonneg (distSq_nonneg x z) hr2.le)
        rw [abs_mul, abs_of_nonneg hc0]
        have h3 := abs_sub (radialTransform (e + 1) (hk k) (euclPot (z - x) / s ^ 2))
          (radialTransform (e + 1) (hk k) (euclPot (z - x) / r ^ 2))
        nlinarith
    exact tendsto_nhds_unique hL (hR.congr fun k => (hEq k).symm)
end RegLelongAnnulus
end GroundTheory.Heights₂.Heights
