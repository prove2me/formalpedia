-- Prove2me | solution 1 for WassersteinDRO.Gelbrich.gelbrich_bound
-- status  : ACCEPTED   (disprove)
-- author  : @moona3k
-- created : 2026-10-06T12:29:23.336873+00:00
-- url     : https://prove2.me/submissions/818bc616-0ffe-4569-85a4-0c29e84d816c

import Definitions.Def_WassersteinDRO_Gelbrich_IsElliptical
import Definitions.Def_WassersteinDRO_Gelbrich_covarianceMatrix
import Definitions.Def_WassersteinDRO_Gelbrich_meanVector
import Definitions.Def_WassersteinDRO_Gelbrich_psdSqrt
import Definitions.Def_WassersteinDRO_Gelbrich_wassersteinDistance
import Mathlib

-- Complete local proof: Solutions.Gelbrich_MassCounter
set_option autoImplicit false
open MeasureTheory
noncomputable section
namespace GelbrichMassCodex
abbrev SingleSpace := EuclideanSpace ℝ (Fin 1)
def unitPoint : SingleSpace := WithLp.toLp 2 (fun _ => (1 : ℝ))
def Q0 : Measure SingleSpace := ENNReal.ofReal 2 • Measure.dirac 0
def Q1 : Measure SingleSpace := ENNReal.ofReal 2 • Measure.dirac unitPoint
lemma mean_Q0 : WassersteinDRO.Gelbrich.meanVector Q0 = 0 := by
  simp [WassersteinDRO.Gelbrich.meanVector, Q0, integral_smul_measure]
lemma mean_Q1 : WassersteinDRO.Gelbrich.meanVector Q1 = (2 : ℝ) • unitPoint := by
  simp [WassersteinDRO.Gelbrich.meanVector, Q1, integral_smul_measure]
lemma covariance_Q0 : WassersteinDRO.Gelbrich.covarianceMatrix Q0 = 0 := by
  unfold WassersteinDRO.Gelbrich.covarianceMatrix
  rw [mean_Q0]
  ext i j
  simp [Q0, integral_smul_measure]
lemma covariance_Q1 : WassersteinDRO.Gelbrich.covarianceMatrix Q1 = Matrix.diagonal (fun _ : Fin 1 => (2 : ℝ)) := by
  unfold WassersteinDRO.Gelbrich.covarianceMatrix
  rw [mean_Q1]
  ext i j
  fin_cases i
  fin_cases j
  norm_num [Q1, integral_smul_measure, unitPoint, Matrix.diagonal]
lemma covariances_psd : (WassersteinDRO.Gelbrich.covarianceMatrix Q0).PosSemidef ∧
    (WassersteinDRO.Gelbrich.covarianceMatrix Q1).PosSemidef := by
  rw [covariance_Q0,covariance_Q1]
  exact ⟨Matrix.PosSemidef.zero, Matrix.PosSemidef.diagonal (fun _ => by norm_num)⟩
lemma norm_unitPoint : ‖unitPoint‖ = 1 := by
  rw [PiLp.norm_eq_of_L2]
  norm_num [unitPoint, Fin.sum_univ_one]
lemma wasserstein_Q0_Q1_le : WassersteinDRO.Gelbrich.wassersteinDistance 2 Q0 Q1 ≤
    ENNReal.ofReal (Real.sqrt 2) := by
  let π : Measure (SingleSpace × SingleSpace) := ENNReal.ofReal 2 • Measure.dirac (0,unitPoint)
  have hf : π.map Prod.fst = Q0 := by
    simp [π, Q0, Measure.map_smul, Measure.map_dirac' measurable_fst]
  have hs : π.map Prod.snd = Q1 := by
    simp [π, Q1, Measure.map_smul, Measure.map_dirac' measurable_snd]
  have hc : (∫⁻ z : SingleSpace × SingleSpace,
      ENNReal.ofReal (‖z.1-z.2‖^(2 : ℝ)) ∂π) = ENNReal.ofReal 2 := by
    dsimp [π]
    rw [lintegral_smul_measure, lintegral_dirac]
    simp only [smul_eq_mul, zero_sub, norm_neg, norm_unitPoint, Real.one_rpow, ENNReal.ofReal_one, mul_one]
  unfold WassersteinDRO.Gelbrich.wassersteinDistance
  have hb : (⨅ (ρ : Measure (SingleSpace × SingleSpace)) (_ : ρ.map Prod.fst = Q0 ∧ ρ.map Prod.snd = Q1),
      ∫⁻ z, ENNReal.ofReal (‖z.1-z.2‖^(2 : ℝ)) ∂ρ) ≤ ENNReal.ofReal 2 :=
    iInf_le_of_le π (iInf_le_of_le ⟨hf,hs⟩ (le_of_eq hc))
  have hp := ENNReal.rpow_le_rpow hb (by norm_num : (0:ℝ) ≤ 1/2)
  calc
    _ ≤ (ENNReal.ofReal (2 : ℝ)) ^ (1 / (2 : ℝ)) := hp
    _ = ENNReal.ofReal (Real.sqrt 2) := by
      rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : (0:ℝ) ≤ 2)
        (by norm_num : (0:ℝ) ≤ 1/2), Real.sqrt_eq_rpow]
#print axioms mean_Q0
#print axioms mean_Q1
#print axioms covariance_Q0
#print axioms covariance_Q1
#print axioms covariances_psd
#print axioms norm_unitPoint
#print axioms wasserstein_Q0_Q1_le
end GelbrichMassCodex

-- Complete local proof: Solutions.Gelbrich_PsdSqrt
set_option autoImplicit false
open WassersteinDRO.Gelbrich
noncomputable section
namespace GelbrichCodex
lemma psdSqrt_zero {m : ℕ} : psdSqrt (0 : Matrix (Fin m) (Fin m) ℝ) = 0 := by
  unfold psdSqrt
  split_ifs with h
  · apply Matrix.conjTranspose_mul_self_eq_zero.mp
    simpa only [h.choose_spec.1.isHermitian.eq] using h.choose_spec.2
  · rfl
lemma psdSqrt_of_not_psd {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ) (hA : ¬ A.PosSemidef) :
    psdSqrt A = 0 := by
  have hn : ¬ ∃ B : Matrix (Fin m) (Fin m) ℝ, B.PosSemidef ∧ B * B = A := by
    rintro ⟨B,hB,he⟩
    apply hA
    rw [← he]
    simpa only [pow_two] using hB.pow 2
  simp only [psdSqrt, dif_neg hn]
#print axioms psdSqrt_zero
#print axioms psdSqrt_of_not_psd
end GelbrichCodex

-- Complete local proof: Solutions.Gelbrich_MassLowerExpression
set_option autoImplicit false
open WassersteinDRO.Gelbrich
noncomputable section
namespace GelbrichMassCodex
lemma lower_expression :
    ‖meanVector Q0 - meanVector Q1‖^2 +
      (covarianceMatrix Q0 + covarianceMatrix Q1 - (2 : ℝ) •
        psdSqrt (psdSqrt (covarianceMatrix Q0) * covarianceMatrix Q1 *
          psdSqrt (covarianceMatrix Q0))).trace = 6 := by
  simp only [mean_Q0, mean_Q1, covariance_Q0, covariance_Q1, GelbrichCodex.psdSqrt_zero,
    zero_mul, mul_zero, smul_zero, sub_zero, zero_add, zero_sub, norm_neg, norm_smul,
    Real.norm_eq_abs, norm_unitPoint]
  norm_num [Matrix.trace, Matrix.diag, Matrix.diagonal, Fin.sum_univ_one]
#print axioms lower_expression
end GelbrichMassCodex

-- Complete local proof: Solutions.Dis_WassersteinDRO_Gelbrich_gelbrich_bound
set_option autoImplicit false
open MeasureTheory WassersteinDRO.Gelbrich
noncomputable section
theorem solution : ¬ (∀ {m : ℕ} (Q Q' : Measure (EuclideanSpace ℝ (Fin m)))
    (μ μ' : EuclideanSpace ℝ (Fin m)) (S S' : Matrix (Fin m) (Fin m) ℝ)
    (hS : S.PosSemidef) (hS' : S'.PosSemidef)
    (hμ : meanVector Q = μ) (hμ' : meanVector Q' = μ')
    (hSeq : covarianceMatrix Q = S) (hS'eq : covarianceMatrix Q' = S'),
    wassersteinDistance 2 Q Q' ≥
      ENNReal.ofReal (Real.sqrt (‖μ - μ'‖ ^ 2 +
        (S + S' - (2 : ℝ) • psdSqrt (psdSqrt S * S' * psdSqrt S)).trace)) ∧
    (∀ g : ℝ → ℝ, IsElliptical Q g μ S → IsElliptical Q' g μ' S' →
      wassersteinDistance 2 Q Q' =
        ENNReal.ofReal (Real.sqrt (‖μ - μ'‖ ^ 2 +
          (S + S' - (2 : ℝ) • psdSqrt (psdSqrt S * S' * psdSqrt S)).trace)))) := by
  intro h
  have hh := (h (m := 1) GelbrichMassCodex.Q0 GelbrichMassCodex.Q1
    (meanVector GelbrichMassCodex.Q0) (meanVector GelbrichMassCodex.Q1)
    (covarianceMatrix GelbrichMassCodex.Q0) (covarianceMatrix GelbrichMassCodex.Q1)
    GelbrichMassCodex.covariances_psd.1 GelbrichMassCodex.covariances_psd.2 rfl rfl rfl rfl).1
  rw [GelbrichMassCodex.lower_expression] at hh
  have hu := hh.trans GelbrichMassCodex.wasserstein_Q0_Q1_le
  have hr : Real.sqrt 6 ≤ Real.sqrt 2 :=
    (ENNReal.ofReal_le_ofReal_iff (Real.sqrt_nonneg 2)).mp hu
  have hs : Real.sqrt 2 < Real.sqrt 6 :=
    Real.sqrt_lt_sqrt (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) < 6)
  exact (not_le_of_gt hs) hr
#print axioms solution
