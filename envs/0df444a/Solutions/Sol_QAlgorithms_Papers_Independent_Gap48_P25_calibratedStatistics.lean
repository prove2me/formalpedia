-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P25.calibratedStatistics
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung
-- created : 2026-10-21T23:22:10.67985+00:00
-- url     : https://prove2.me/submissions/ddfca8ac-3997-4b51-b085-16e58ab7c750

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P25

open QAlgorithms.Papers.Independent.Gap48.P25
noncomputable section


open scoped BigOperators ComplexConjugate

open Filter

open QAlgorithms.Papers.Independent.Claimed50.P08 (classicalEntropy)

/-- Eqs.(44)–(48), PDF p.31: calibrated statistical ratio, with IV.C's distinct
Y_n convention and independent dark-count law. Footnote 57 excludes photon
creation on vacuum inputs, so f 0 = 0; no operational security conclusion. -/
theorem solution (p : PhotonLaw) (nu b pd : ℝ) (f e : ℕ → ℝ)
    (hnu : 0 < nu) (hb : b ∈ Set.Icc (0 : ℝ) 1) (hpd : 0 ≤ pd ∧ pd < 1/2)
    (hf : ∀ n, f n ∈ Set.Icc (0 : ℝ) 1) (hf0 : f 0 = 0)
    (he : ∀ n, e n ∈ Set.Icc (0 : ℝ) 1)
    (hR : 0 < calibratedTotal p nu b pd f) :
    let R := calibratedTotal p nu b pd f
    let Y := calibratedFraction p nu b pd f
    let delta := (1-Y)/2
    let photonWrong := ∑' n, calibratedPhoton p nu b f n*e n
    let dark := ∑' n, calibratedDark p nu b pd f n
    Y ∈ Set.Icc (0 : ℝ) 1 ∧ Y = (1-2*pd*nu/R)/(1-2*pd) ∧
    dark/R = 2*delta ∧ (photonWrong+dark/2)/R = (photonWrong/R)+delta ∧
    (0 < Y → (photonWrong+dark/2)/R = Y*(photonWrong/(R*Y))+delta) := by
  intro R Y delta photonWrong dark
  have hpS : Summable p.mass := p.normalized.summable
  have hp1 : ∑' n, p.mass n = 1 := p.normalized.tsum_eq
  have hpf : Summable (fun n => p.mass n * f n) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg (p.nonnegative n) (hf n).1)
      (fun n => mul_le_of_le_one_right (p.nonnegative n) (hf n).2) hpS
  set S := ∑' n, p.mass n * f n with hSdef
  have hS0 : 0 ≤ S := tsum_nonneg (fun n => mul_nonneg (p.nonnegative n) (hf n).1)
  have hS1 : S ≤ 1 := by
    rw [← hp1]; exact hpf.tsum_le_tsum (fun n => mul_le_of_le_one_right (p.nonnegative n) (hf n).2) hpS
  have hph_eq : (fun n => calibratedPhoton p nu b f n) = fun n => (nu*b) * (p.mass n * f n) := by
    funext n; unfold calibratedPhoton; ring
  have hdk_eq : (fun n => calibratedDark p nu b pd f n) =
      fun n => (2*pd*nu) * p.mass n - (2*pd*nu*b) * (p.mass n * f n) := by
    funext n; unfold calibratedDark; ring
  have hphS : Summable (fun n => calibratedPhoton p nu b f n) := by
    rw [hph_eq]; exact hpf.mul_left _
  have hdkS : Summable (fun n => calibratedDark p nu b pd f n) := by
    rw [hdk_eq]; exact (hpS.mul_left _).sub (hpf.mul_left _)
  have hph : ∑' n, calibratedPhoton p nu b f n = nu*b*S := by
    rw [hph_eq, tsum_mul_left]
  have hdk : dark = 2*pd*nu*(1-b*S) := by
    simp only [dark]; rw [hdk_eq, (hpS.mul_left _).tsum_sub (hpf.mul_left _), tsum_mul_left,
      tsum_mul_left, hp1]; ring
  have hRe : R = nu*b*S + 2*pd*nu*(1-b*S) := by
    simp only [R, calibratedTotal]; rw [hphS.tsum_add hdkS, hph]; rw [← hdk]
  have hY : Y = nu*b*S/R := by simp only [Y, calibratedFraction]; rw [hph]
  have hRpos : 0 < R := hR
  have hb0 := hb.1
  have hbS : b*S ≤ 1 := by nlinarith [hb.2]
  have hd0 : 0 ≤ dark := by rw [hdk]; exact mul_nonneg (mul_nonneg (by linarith [hpd.1]) hnu.le) (by linarith)
  have hpd2 : 0 < 1 - 2*pd := by linarith [hpd.2]
  have hR2 : R - nu*b*S = dark := by rw [hRe, hdk]; ring
  refine ⟨⟨?_, ?_⟩, ?_, ?_, ?_, fun hYp => ?_⟩
  · rw [hY]; positivity
  · rw [hY, div_le_one hRpos, ← sub_nonneg, hR2]; exact hd0
  · rw [hY]; field_simp; rw [hRe]; ring
  · simp only [delta]; rw [hY]; field_simp; linarith
  · simp only [delta]; rw [hY]; field_simp; linarith
  · rw [show Y*(photonWrong/(R*Y)) = photonWrong/R by field_simp]
    simp only [delta]; rw [hY]; field_simp; linarith




