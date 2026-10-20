-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P50.remark_4_4
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:22:28.924193+00:00
-- url     : https://prove2.me/submissions/0c676d30-cb59-4a2c-93f9-8a657cdbb790

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P50

open scoped Matrix.Norms.L2Operator in
lemma g53i_specNorm_alg (g : ℝ) : specNorm (algebraMap ℝ (M 1) g) = |g| := by
  unfold specNorm
  rw [norm_algebraMap']
  simp

lemma g53i_sqrt_ratio (d : ℝ) (hd : 0 < d) :
    Real.sqrt (d * (1 - d)) / Real.sqrt d = Real.sqrt (1 - d) := by
  have : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  rw [Real.sqrt_mul hd.le]; field_simp

/-- Remark 4.4, source PDF p.14: sharpness of the operator estimate, without asserting
sharpness of the channel fidelity bound. The denominator in the ratio is sqrt(delta). -/
theorem solution :
    (∀ delta ∈ Icc (0 : ℝ) 1,
      specNorm (cfc gHash ((delta : ℂ) • (1 : M 1)) - cfc gHash (0 : M 1)) =
        Real.sqrt (delta * (1 - delta))) ∧
    Tendsto (fun delta : ℝ => Real.sqrt (delta * (1 - delta)) / Real.sqrt delta)
      (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
    (∀ C : ℝ, 0 ≤ C → C < 1 → ∃ delta ∈ Ioo (0 : ℝ) 1,
      C * Real.sqrt delta < Real.sqrt (delta * (1 - delta))) ∧
    (∀ beta : ℝ, 1 / 2 < beta → ∀ C : ℝ, 0 < C → ∃ delta ∈ Ioo (0 : ℝ) 1,
      C * Real.rpow delta beta < Real.sqrt (delta * (1 - delta))) := by
  have hsq1 : Tendsto (fun d : ℝ => Real.sqrt (1 - d)) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have : Tendsto (fun d : ℝ => Real.sqrt (1 - d)) (𝓝 (0 : ℝ)) (𝓝 1) := by
      have hc : Continuous (fun d : ℝ => Real.sqrt (1 - d)) := by fun_prop
      simpa using hc.tendsto (0 : ℝ)
    exact this.mono_left nhdsWithin_le_nhds
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro d _
    have h1 : ((d : ℂ) • (1 : M 1)) = algebraMap ℝ (M 1) d := by
      rw [Algebra.algebraMap_eq_smul_one]; ext i j; simp [Matrix.one_apply]
    rw [h1, cfc_algebraMap, cfc_apply_zero]
    have h0 : gHash 0 = 0 := by simp [gHash]
    rw [h0, map_zero, sub_zero, g53i_specNorm_alg]
    unfold gHash
    exact abs_of_nonneg (Real.sqrt_nonneg _)
  · refine hsq1.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with d hd
    exact (g53i_sqrt_ratio d hd).symm
  · intro C hC0 hC1
    refine ⟨(1 - C ^ 2) / 2, ⟨by nlinarith, by nlinarith⟩, ?_⟩
    set d := (1 - C ^ 2) / 2 with hd
    have hdpos : 0 < d := by rw [hd]; nlinarith
    rw [Real.sqrt_mul hdpos.le, mul_comm C]
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hdpos
    refine mul_lt_mul_of_pos_left ?_ hs
    rw [show C = Real.sqrt (C ^ 2) by rw [Real.sqrt_sq hC0]]
    exact Real.sqrt_lt_sqrt (sq_nonneg _) (by rw [hd]; nlinarith)
  · intro beta hb C hC
    have hpow : Tendsto (fun d : ℝ => C * d ^ (beta - 1 / 2)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      have h := ((Real.continuousAt_rpow_const (0:ℝ) (beta - 1/2)
        (Or.inr (by linarith))).tendsto).const_mul C
      rw [Real.zero_rpow (by linarith), mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    have ev1 : ∀ᶠ d in 𝓝[>] (0 : ℝ), C * d ^ (beta - 1 / 2) < 1 / 2 :=
      hpow.eventually (gt_mem_nhds (by norm_num))
    have ev2 : ∀ᶠ d in 𝓝[>] (0 : ℝ), 1 / 2 < Real.sqrt (1 - d) :=
      hsq1.eventually (lt_mem_nhds (by norm_num))
    have ev3 : ∀ᶠ d in 𝓝[>] (0 : ℝ), d < 1 :=
      (tendsto_id.mono_left nhdsWithin_le_nhds).eventually (gt_mem_nhds (by norm_num))
    obtain ⟨d, h1, h2, h3, h4⟩ := (ev1.and (ev2.and (ev3.and self_mem_nhdsWithin))).exists
    refine ⟨d, ⟨h4, h3⟩, ?_⟩
    have hd0 : (0:ℝ) < d := h4
    have : Real.rpow d beta = d ^ (beta - 1 / 2) * Real.sqrt d := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add hd0]; simp
    rw [this, Real.sqrt_mul hd0.le, ← mul_assoc, mul_comm (Real.sqrt d) (Real.sqrt (1 - d))]
    have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
    exact mul_lt_mul_of_pos_right (by linarith) hs

end
