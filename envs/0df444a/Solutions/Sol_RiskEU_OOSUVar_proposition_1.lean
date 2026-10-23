-- Prove2me | solution 1 for RiskEU.OOSUVar.proposition_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-22T11:01:35.445904+00:00
-- url     : https://prove2.me/submissions/06057154-039f-44d9-a71b-f8316bf88a24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_RiskEU_OOSUVar_Setting
import Theorems.Thm_RiskEU_OOSUVar_eq_IA44
import Theorems.Thm_RiskEU_OOSUVar_eq_IA59
import Theorems.Thm_RiskEU_OOSUVar_eq_IA68

open MeasureTheory ProbabilityTheory Matrix RiskEU.OOSUVar

/-- U(w) = oosMean − (γ/2) oosVar, pointwise. -/
private lemma U_wShrink_eq {N T : ℕ} (M : Market N) (κ : ℝ) (x : Fin T → Fin N → ℝ) :
    M.U (M.wShrink κ x) = M.oosMean κ x - M.gamma / 2 * M.oosVar κ x := rfl

private lemma wShrink_zero {N T : ℕ} (M : Market N) (x : Fin T → Fin N → ℝ) :
    M.wShrink 0 x = wHatG x := by
  simp [Market.wShrink]

private lemma var_U {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (fun ω => M.U (M.wShrink κ (sampleData r ω))) 2 P ∧
    variance (fun ω => M.U (M.wShrink κ (sampleData r ω))) P =
      varGMV M.gamma T N M.sigmaG2 M.psi2 + Delta M.gamma T N M.sigmaG2 M.psi2 κ := by
  obtain ⟨hX, hVX⟩ := eq_IA44 M hM P r hr κ hκ
  obtain ⟨hY, hVY⟩ := eq_IA59 M hM P r hr κ hκ
  obtain ⟨-, -, hC⟩ := eq_IA68 M hM P r hr κ hκ
  set X := fun ω => M.oosMean κ (sampleData r ω) with hXdef
  set Y := fun ω => M.oosVar κ (sampleData r ω) with hYdef
  have hfun : (fun ω => M.U (M.wShrink κ (sampleData r ω))) =
      X - (fun ω => M.gamma / 2 * Y ω) := by
    funext ω; simp [X, Y, U_wShrink_eq]
  have hY' : MemLp (fun ω => M.gamma / 2 * Y ω) 2 P := hY.const_mul _
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hX.sub hY'
  rw [hfun, variance_sub hX hY', covariance_const_mul_right, variance_const_mul, hVX, hVY, hC]
  obtain ⟨hN2, hNT, -, hγ⟩ := hM
  have hTN : (N : ℝ) + 7 < T := by exact_mod_cast hNT
  have h0 : (T : ℝ) - N ≠ 0 := by intro h; linarith
  have h1 : (T : ℝ) - N - 1 ≠ 0 := by intro h; linarith
  have h2 : (T : ℝ) - N - 2 ≠ 0 := by intro h; linarith
  have h3 : (T : ℝ) - N - 3 ≠ 0 := by intro h; linarith
  have h5 : (T : ℝ) - N - 5 ≠ 0 := by intro h; linarith
  have h7 : (T : ℝ) - N - 7 ≠ 0 := by intro h; linarith
  have hg : M.gamma ≠ 0 := hγ.ne'
  simp only [varGMV, Delta, a1, a2, a3, a4]
  field_simp
  ring

theorem solution {N T : ℕ} (M : Market N) (hM : M.Standing T)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (r : Fin T → Ω → EuclideanSpace ℝ (Fin N)) (hr : M.IsGaussianSample P r)
    (κ : ℝ) (hκ : κ ∈ Set.Icc (0 : ℝ) 1) :
    MemLp (fun ω => M.U (M.wShrink κ (sampleData r ω))) 2 P ∧
    variance (fun ω => M.U (M.wShrink κ (sampleData r ω))) P =
      varGMV M.gamma T N M.sigmaG2 M.psi2 + Delta M.gamma T N M.sigmaG2 M.psi2 κ ∧
    MemLp (fun ω => M.U (wHatG (sampleData r ω))) 2 P ∧
    variance (fun ω => M.U (wHatG (sampleData r ω))) P =
      varGMV M.gamma T N M.sigmaG2 M.psi2 := by
  obtain ⟨h1, h2⟩ := var_U M hM P r hr κ hκ
  obtain ⟨h3, h4⟩ := var_U M hM P r hr 0 ⟨le_refl 0, zero_le_one⟩
  simp only [wShrink_zero] at h3 h4
  refine ⟨h1, h2, h3, ?_⟩
  rw [h4]
  simp [Delta]
