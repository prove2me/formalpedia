-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P50.lc_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T20:59:16.659432+00:00
-- url     : https://prove2.me/submissions/f3deae5e-483c-45f0-b1b7-f6f0f915f4bb

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

namespace QAlgorithms.Papers.Independent.Information100.P50

lemma X7V_atZero_lc : atZero lcGenerator = 1 := by
  unfold atZero
  have hc : ContinuousAt lcGenerator 0 := by
    unfold lcGenerator
    apply ContinuousAt.div (by fun_prop) (by fun_prop)
    norm_num
  have h : Tendsto lcGenerator (𝓝[>] (0:ℝ)) (𝓝 (lcGenerator 0)) :=
    hc.tendsto.mono_left nhdsWithin_le_nhds
  rw [h.limUnder_eq]
  norm_num [lcGenerator]

lemma X7V_atInf_lc : atInfinity lcGenerator = 1 := by
  unfold atInfinity
  have hg : Tendsto (fun s : ℝ => (1 - s) ^ 2 / (1 + s)) (𝓝[>] (0:ℝ)) (𝓝 1) := by
    have hc : ContinuousAt (fun s : ℝ => (1 - s) ^ 2 / (1 + s)) 0 := by
      apply ContinuousAt.div (by fun_prop) (by fun_prop)
      norm_num
    have := hc.tendsto.mono_left (nhdsWithin_le_nhds (s := Ioi (0:ℝ)))
    simpa using this
  have h2 := hg.comp tendsto_inv_atTop_nhdsGT_zero
  have h3 : Tendsto (fun t : ℝ => lcGenerator t / t) atTop (𝓝 1) := by
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (0:ℝ)] with t ht
    simp only [Function.comp, lcGenerator]
    field_simp
  exact h3.limUnder_eq

lemma X7V_persp_eq : convexPerspective lcGenerator = fun t : ℝ => (2 * t - 1) ^ 2 := by
  funext t
  unfold convexPerspective
  by_cases h0 : t = 0
  · subst h0; simp [X7V_atZero_lc]
  by_cases h1 : t = 1
  · subst h1; simp [X7V_atInf_lc]; norm_num
  simp only [h0, h1, if_false, lcGenerator]
  have h1' : (1 - t) ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  field_simp
  ring

lemma X7V_cfc_eq {n : ℕ} (E : M n) (hE : E.IsHermitian) :
    cfc (convexPerspective lcGenerator) E = ((2:ℂ) • E - 1) ^ 2 := by
  rw [X7V_persp_eq]
  have hsa : IsSelfAdjoint E := hE
  rw [cfc_pow (fun t : ℝ => 2 * t - 1) 2 E, cfc_sub (fun t : ℝ => 2 * t) (fun _ => (1:ℝ)) E,
    cfc_const_mul (2:ℝ) (fun t : ℝ => t) E, cfc_id' ℝ E, cfc_const_one ℝ E]
  congr 2

open scoped Matrix.Norms.L2Operator MatrixOrder in
lemma X7V_norm_le_one {n : ℕ} (E : M n) (hE : IsEffect E) : ‖(2:ℂ) • E - 1‖ ≤ 1 := by
  set A := (2:ℂ) • E - 1 with hA
  have hH : Aᴴ = A := by
    rw [hA, Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, hE.1.isHermitian.eq,
      Matrix.conjTranspose_one]
    simp
  -- 1 - A^H A = 4 (E - E^2) is PSD
  have hpsd : (1 - Aᴴ * A).PosSemidef := by
    have h1 : ((1 - E) * E * (1 - E)).PosSemidef := by
      have := hE.1.conjTranspose_mul_mul_same (1 - E)
      rwa [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hE.1.isHermitian.eq] at this
    have h2 : (E * (1 - E) * E).PosSemidef := by
      have := hE.2.conjTranspose_mul_mul_same E
      rwa [hE.1.isHermitian.eq] at this
    have h3 := (h1.add h2).smul (show (0:ℂ) ≤ 4 by norm_num)
    convert h3 using 1
    rw [hH, hA]
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_sub,
      smul_add, smul_smul]
    module
  have hnn : (0 : M n) ≤ Aᴴ * A := by
    rw [Matrix.nonneg_iff_posSemidef]; exact Matrix.posSemidef_conjTranspose_mul_self A
  have hle : Aᴴ * A ≤ algebraMap ℝ (M n) 1 := by
    rw [map_one, Matrix.le_iff]; exact hpsd
  have hn : ‖Aᴴ * A‖ ≤ 1 := (CStarAlgebra.norm_le_iff_le_algebraMap (Aᴴ * A) zero_le_one hnn).mpr hle
  rw [Matrix.l2_opNorm_conjTranspose_mul_self] at hn
  nlinarith [norm_nonneg A]

open scoped Matrix.Norms.L2Operator in
lemma X7V_main {n : ℕ} (E F : M n) (hE : IsEffect E) (hF : IsEffect F) :
    ‖((2:ℂ) • E - 1) ^ 2 - ((2:ℂ) • F - 1) ^ 2‖ ≤ 4 * ‖E - F‖ := by
  set A := (2:ℂ) • E - 1
  set B := (2:ℂ) • F - 1
  have hAB : A - B = (2:ℂ) • (E - F) := by simp only [A, B, smul_sub]; abel
  have key : A ^ 2 - B ^ 2 = A * (A - B) + (A - B) * B := by noncomm_ring
  rw [key, hAB]
  have hA := X7V_norm_le_one E hE
  have hB := X7V_norm_le_one F hF
  have h2 : ‖(2:ℂ) • (E - F)‖ = 2 * ‖E - F‖ := by rw [norm_smul]; norm_num
  calc ‖A * ((2:ℂ) • (E - F)) + (2:ℂ) • (E - F) * B‖
      ≤ ‖A‖ * ‖(2:ℂ) • (E - F)‖ + ‖(2:ℂ) • (E - F)‖ * ‖B‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
    _ ≤ 1 * (2 * ‖E - F‖) + (2 * ‖E - F‖) * 1 := by
        rw [h2]
        have := norm_nonneg (E - F)
        gcongr
    _ = 4 * ‖E - F‖ := by ring

end QAlgorithms.Papers.Independent.Information100.P50

end

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P50 in
theorem solution {n : ℕ} (E F : M n) (hE : IsEffect E) (hF : IsEffect F) :
    specNorm (cfc (convexPerspective lcGenerator) E - cfc (convexPerspective lcGenerator) F) ≤
      4 * specNorm (E - F) := by
  rw [X7V_cfc_eq E hE.1.isHermitian, X7V_cfc_eq F hF.1.isHermitian]
  exact X7V_main E F hE hF

end
