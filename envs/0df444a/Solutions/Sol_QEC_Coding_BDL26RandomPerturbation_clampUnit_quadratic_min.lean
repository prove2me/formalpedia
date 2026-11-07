-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.clampUnit_quadratic_min
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:43:12.978483+00:00
-- url     : https://prove2.me/submissions/a6b4c0a8-dffd-4c09-9dff-eae2daccac95

import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_TriangleGeometry
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SegmentProjection
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {Q D t : ℝ} (hQ : 0 < Q) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    Q*(clampUnit (D/Q))^2-2*D*clampUnit (D/Q) ≤ Q*t^2-2*D*t := by
  by_cases hD : D ≤ 0
  · have hd : D/Q ≤ 0 := div_nonpos_of_nonpos_of_nonneg hD hQ.le
    have hc : clampUnit (D/Q) = 0 := max_eq_left ((min_le_right _ _).trans hd)
    rw [hc]
    have hprod := mul_nonpos_of_nonpos_of_nonneg hD ht0
    have hsq := mul_nonneg hQ.le (sq_nonneg t)
    nlinarith
  · have hD0 : 0 < D := lt_of_not_ge hD
    by_cases hDQ : Q ≤ D
    · have hd : 1 ≤ D/Q := (le_div_iff₀ hQ).mpr (by simpa using hDQ)
      have hc : clampUnit (D/Q) = 1 := by simp [clampUnit,min_eq_left hd]
      rw [hc]
      have hsq := mul_nonneg hQ.le (sq_nonneg (t-1))
      have hprod := mul_nonneg (sub_nonneg.mpr hDQ) (sub_nonneg.mpr ht1)
      nlinarith
    · have hd0 : 0 ≤ D/Q := (div_pos hD0 hQ).le
      have hd1 : D/Q ≤ 1 := (div_le_iff₀ hQ).mpr (by linarith)
      have hc : clampUnit (D/Q) = D/Q := by simp [clampUnit,min_eq_right hd1,max_eq_right hd0]
      rw [hc]
      have he : Q*(D/Q) = D := by field_simp [hQ.ne']
      have hsq := mul_nonneg hQ.le (sq_nonneg (t-D/Q))
      have het := congrArg (fun x : ℝ => x*t) he
      have hec := congrArg (fun x : ℝ => x*(D/Q)) he
      nlinarith
end QEC.Coding.BDL26RandomPerturbation
