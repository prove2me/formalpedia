-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P50.remark_5_11
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T03:15:33.588982+00:00
-- url     : https://prove2.me/submissions/d8f36663-b4c3-475d-b016-4eac48bac12b

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P50

noncomputable section

open scoped Matrix ComplexConjugate ENNReal Topology ComplexOrder Kronecker

open Filter Set

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P50

lemma g53e_hel0 : atZero hellingerGenerator = 1 := by
  unfold atZero
  apply Tendsto.limUnder_eq
  have : Continuous hellingerGenerator := by unfold hellingerGenerator; fun_prop
  have h := this.continuousWithinAt (s := Set.Ioi 0) (x := 0)
  simpa [hellingerGenerator] using h.tendsto

lemma g53e_helI : atInfinity hellingerGenerator = 1 := by
  unfold atInfinity
  apply Tendsto.limUnder_eq
  have h1 : Tendsto (fun t : ℝ => (Real.sqrt t)⁻¹) atTop (𝓝 0) := by
    exact tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop)
  have h2 : Tendsto (fun t : ℝ => ((Real.sqrt t)⁻¹ - 1) ^ 2) atTop (𝓝 1) := by
    have := (h1.sub_const 1).pow 2
    simpa using this
  apply h2.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  unfold hellingerGenerator
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hst : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  have key : ((Real.sqrt t)⁻¹ - 1) ^ 2 = (1 - Real.sqrt t) ^ 2 / (Real.sqrt t) ^ 2 := by
    field_simp
  rw [key, hst]

lemma g53e_al0 (a : ℝ) (ha : 0 < a) (ha1 : a < 1) : atZero (alphaGenerator a) = 1 / (1 - a) := by
  unfold atZero
  apply Tendsto.limUnder_eq
  have hc : ContinuousAt (fun t : ℝ => Real.rpow t a) 0 := Real.continuousAt_rpow_const 0 a (Or.inr ha.le)
  have h := ((continuousAt_const (y := (1:ℝ)) (x := (0:ℝ)) |>.sub hc).div_const (1 - a)).continuousWithinAt (s := Set.Ioi 0)
  have h0 : Real.rpow 0 a = 0 := Real.zero_rpow ha.ne'
  have := h.tendsto
  have e : (1 - Real.rpow 0 a) / (1 - a) = 1 / (1 - a) := by rw [h0, sub_zero]
  simp only [Pi.sub_apply] at this
  rw [e] at this
  exact this

lemma g53e_alI (a : ℝ) (ha : 0 < a) (ha1 : a < 1) : atInfinity (alphaGenerator a) = 0 := by
  unfold atInfinity
  apply Tendsto.limUnder_eq
  have h1 : Tendsto (fun t : ℝ => t ^ (-(1 - a))) atTop (𝓝 0) := tendsto_rpow_neg_atTop (by linarith)
  have h2 : Tendsto (fun t : ℝ => (t⁻¹ - t ^ (-(1 - a))) / (1 - a)) atTop (𝓝 0) := by
    have := (tendsto_inv_atTop_zero.sub h1).div_const (1 - a)
    simpa using this
  apply h2.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  unfold alphaGenerator
  have e : t ^ (-(1 - a)) = Real.rpow t a / t := by
    rw [show -(1 - a) = a - 1 by ring, Real.rpow_sub_one ht.ne']; rfl
  rw [e]
  have h1a : (1 - a) ≠ 0 := by linarith
  field_simp

lemma g53e_lc0 : atZero lcGenerator = 1 := by
  unfold atZero
  apply Tendsto.limUnder_eq
  have hc : ContinuousAt lcGenerator 0 := by
    unfold lcGenerator
    apply ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  simpa [lcGenerator] using hc.continuousWithinAt.tendsto (s := Set.Ioi 0)

lemma g53e_lcI : atInfinity lcGenerator = 1 := by
  unfold atInfinity
  apply Tendsto.limUnder_eq
  have h2 : Tendsto (fun t : ℝ => (1 - t⁻¹) ^ 2 / (1 + t⁻¹)) atTop (𝓝 1) := by
    have := (((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_sub 1).pow 2).div ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_add 1) (by norm_num)
    simpa [Pi.div_def] using this
  apply h2.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  unfold lcGenerator
  have : t + 1 ≠ 0 := by linarith
  field_simp

lemma g53e_js0 : atZero jsGenerator = Real.log 2 := by
  unfold atZero
  apply Tendsto.limUnder_eq
  have hc : ContinuousAt jsGenerator 0 := by
    unfold jsGenerator
    apply ContinuousAt.sub Real.continuous_mul_log.continuousAt
    apply ContinuousAt.mul (by fun_prop)
    apply ContinuousAt.log (by fun_prop) (by norm_num)
  have := hc.continuousWithinAt.tendsto (s := Set.Ioi 0)
  have e : jsGenerator 0 = Real.log 2 := by
    simp [jsGenerator, Real.log_inv]
  rwa [e] at this

lemma g53e_jsI : atInfinity jsGenerator = Real.log 2 := by
  unfold atInfinity
  apply Tendsto.limUnder_eq
  have hA : Tendsto (fun t : ℝ => Real.log (2 / (1 + t⁻¹))) atTop (𝓝 (Real.log 2)) := by
    have h1 : Tendsto (fun t : ℝ => 2 / (1 + t⁻¹)) atTop (𝓝 2) := by
      have h2 : Tendsto (fun t : ℝ => 2 / (1 + t⁻¹)) atTop (𝓝 (2 / (1 + 0))) :=
        tendsto_const_nhds.div ((tendsto_inv_atTop_zero (𝕜 := ℝ)).const_add 1) (by norm_num)
      simpa using h2
    exact (Real.continuousAt_log (by norm_num)).tendsto.comp h1
  have hB : Tendsto (fun t : ℝ => Real.log ((1 + t) / 2) / t) atTop (𝓝 0) := by
    have hL := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    simp only [pow_one, one_mul, add_zero] at hL
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hL
    · filter_upwards [eventually_ge_atTop 1] with t ht
      apply div_nonneg (Real.log_nonneg (by linarith)) (by linarith)
    · filter_upwards [eventually_ge_atTop 1] with t ht
      apply div_le_div_of_nonneg_right _ (by linarith)
      exact Real.log_le_log (by linarith) (by linarith)
  have := hA.sub hB
  rw [sub_zero] at this
  apply this.congr'
  filter_upwards [eventually_gt_atTop 0] with t ht
  unfold jsGenerator
  have e1 : 2 / (1 + t⁻¹) = t / ((1 + t) / 2) := by field_simp; ring
  rw [e1, Real.log_div ht.ne' (by positivity)]
  field_simp
  ring

lemma g53e_pt1 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    convexPerspective hellingerGenerator t = 1 - 2 * gHash t := by
  unfold convexPerspective
  split_ifs with ha hb
  · subst ha; simp [g53e_hel0, gHash]
  · subst hb; simp [g53e_helI, gHash]
  · have hu : 0 < 1 - t := by rcases lt_or_eq_of_le h1 with h | h; linarith; exact absurd h hb
    unfold hellingerGenerator gHash
    rw [Real.sqrt_div h0, Real.sqrt_mul h0]
    have hsu := Real.sqrt_pos.mpr hu
    have e1 := Real.sq_sqrt hu.le
    have e2 := Real.sq_sqrt h0
    field_simp
    nlinarith [e1, e2]

lemma g53e_pt2 (a : ℝ) (ha : 0 < a) (ha1 : a < 1) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    convexPerspective (alphaGenerator a) t = (1 - a)⁻¹ * ((1 - t) - hAlpha a t) := by
  unfold convexPerspective hAlpha
  have h1a : (1 - a) ≠ 0 := by linarith
  split_ifs with hz hb
  · subst hz; rw [g53e_al0 a ha ha1]
    simp [Real.zero_rpow ha.ne']
  · subst hb; rw [g53e_alI a ha ha1]
    simp [Real.zero_rpow (show (1 - a) ≠ 0 by linarith)]
  · have hu : 0 < 1 - t := by rcases lt_or_eq_of_le h1 with h | h; linarith; exact absurd h hb
    unfold alphaGenerator
    have e1 : Real.rpow (t / (1 - t)) a = Real.rpow t a / Real.rpow (1 - t) a := Real.div_rpow h0 hu.le a
    have e2 : Real.rpow (1 - t) (1 - a) = (1 - t) / Real.rpow (1 - t) a := by
      have := Real.rpow_sub hu 1 a
      rw [Real.rpow_one] at this; exact this
    rw [e1, e2]
    have hp : 0 < Real.rpow (1 - t) a := Real.rpow_pos_of_pos hu a
    field_simp

lemma g53e_pt3 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    convexPerspective lcGenerator t = (2 * t - 1) ^ 2 := by
  unfold convexPerspective
  split_ifs with ha hb
  · subst ha; simp [g53e_lc0]
  · subst hb; simp [g53e_lcI]; norm_num
  · have hu : 0 < 1 - t := by rcases lt_or_eq_of_le h1 with h | h; linarith; exact absurd h hb
    unfold lcGenerator
    have : t / (1 - t) + 1 = 1 / (1 - t) := by field_simp; ring
    rw [this]
    field_simp
    ring

lemma g53e_pt4 (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    convexPerspective jsGenerator t = Real.log 2 + t * Real.log t + (1 - t) * Real.log (1 - t) := by
  unfold convexPerspective
  split_ifs with ha hb
  · subst ha; simp [g53e_js0]
  · subst hb; simp [g53e_jsI]
  · have hu : 0 < 1 - t := by rcases lt_or_eq_of_le h1 with h | h; linarith; exact absurd h hb
    have ht : 0 < t := lt_of_le_of_ne h0 (Ne.symm ha)
    unfold jsGenerator
    have e1 : (1 + t / (1 - t)) / 2 = (2 * (1 - t))⁻¹ := by field_simp; ring
    have e2 : 1 + t / (1 - t) = 1 / (1 - t) := by field_simp; ring
    rw [e1, e2, Real.log_inv, Real.log_mul (by norm_num) hu.ne', Real.log_div ht.ne' hu.ne']
    field_simp
    ring

open scoped Matrix ComplexOrder

lemma g53e_spec {r : ℕ} (T : M r) (hT : IsEffect T) : ∀ t ∈ spectrum ℝ T, 0 ≤ t ∧ t ≤ 1 := by
  intro t ht
  have h1 := hT.1
  have h2 := hT.2
  constructor
  · obtain ⟨i, rfl⟩ := h1.1.spectrum_real_eq_range_eigenvalues ▸ ht
    exact h1.eigenvalues_nonneg i
  · have : 1 - t ∈ spectrum ℝ (1 - T) := by
      have := spectrum.singleton_sub_eq T (1 : ℝ)
      rw [map_one] at this
      rw [← this]
      exact Set.sub_mem_sub rfl ht
    obtain ⟨i, hi⟩ := h2.1.spectrum_real_eq_range_eigenvalues ▸ this
    have := h2.eigenvalues_nonneg i
    linarith

/-- Remark 5.11, source PDF p.21; generators are those of Definition 5.10, PDF p.20.
The log terms use the usual 0 log 0 convention. -/
theorem solution {r : ℕ} (T : M r) (hT : IsEffect T)
    (alpha : ℝ) (halpha : 0 < alpha) (halpha1 : alpha < 1) :
    cfc (convexPerspective hellingerGenerator) T = 1 - (2 : ℂ) • cfc gHash T ∧
    cfc (convexPerspective (alphaGenerator alpha)) T =
      ((1 - alpha : ℝ) : ℂ)⁻¹ • ((1 - T) - cfc (hAlpha alpha) T) ∧
    cfc (convexPerspective lcGenerator) T = ((2 : ℂ) • T - 1) ^ 2 ∧
    cfc (convexPerspective jsGenerator) T =
      (Real.log 2 : ℂ) • (1 : M r) + T * cfc Real.log T + (1 - T) * cfc Real.log (1 - T) := by
  have hsp := g53e_spec T hT
  have hsa : IsSelfAdjoint T := hT.1.1
  have hc : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ T) := fun f => Matrix.finite_real_spectrum.continuousOn f
  have h1T : cfc (fun t : ℝ => 1 - t) T = 1 - T := by
    rw [cfc_sub (fun _ => (1 : ℝ)) (fun t => t) T (hf := hc _) (hg := hc _), cfc_const (1:ℝ) T, cfc_id' ℝ T, map_one]
  have hcs : ∀ (c : ℝ) (X : M r), c • X = (c : ℂ) • X := fun c X => (Complex.coe_smul c X).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [cfc_congr (g := fun t => 1 - 2 * gHash t) (fun t ht => g53e_pt1 t (hsp t ht).1 (hsp t ht).2)]
    rw [cfc_sub (fun _ => (1 : ℝ)) (fun t => 2 * gHash t) T (hf := hc _) (hg := hc _), cfc_const (1:ℝ) T, map_one,
      cfc_const_mul 2 gHash T (hc _), hcs]
    norm_num
  · rw [cfc_congr (g := fun t => (1 - alpha)⁻¹ * ((1 - t) - hAlpha alpha t))
      (fun t ht => g53e_pt2 alpha halpha halpha1 t (hsp t ht).1 (hsp t ht).2)]
    rw [cfc_const_mul _ _ T (hc _), cfc_sub (fun t => 1 - t) (hAlpha alpha) T (hf := hc _) (hg := hc _), h1T, hcs]
    push_cast; rfl
  · rw [cfc_congr (g := fun t => (2 * t - 1) ^ 2)
      (fun t ht => g53e_pt3 t (hsp t ht).1 (hsp t ht).2)]
    rw [cfc_pow (fun t => 2 * t - 1) 2 T (hc _), cfc_sub (fun t => 2 * t) (fun _ => (1 : ℝ)) T (hf := hc _) (hg := hc _),
      cfc_const_mul 2 (fun t => t) T (hc _), cfc_id' ℝ T, cfc_const (1:ℝ) T, map_one, hcs]
    norm_num
  · rw [cfc_congr (g := fun t => Real.log 2 + t * Real.log t + (1 - t) * Real.log (1 - t))
      (fun t ht => g53e_pt4 t (hsp t ht).1 (hsp t ht).2)]
    rw [cfc_add (fun t => Real.log 2 + t * Real.log t) (fun t => (1 - t) * Real.log (1 - t)) (a := T) (hf := hc _) (hg := hc _),
      cfc_add (fun _ => Real.log 2) (fun t => t * Real.log t) (a := T) (hf := hc _) (hg := hc _),
      cfc_mul (fun t => t) Real.log T (hc _) (hc _),
      cfc_mul (fun t => 1 - t) (fun t => Real.log (1 - t)) T (hc _) (hc _), cfc_const (Real.log 2) T, cfc_id' ℝ T, h1T]
    have hcomp : cfc (fun t => Real.log (1 - t)) T = cfc Real.log (1 - T) := by
      rw [← h1T]
      exact cfc_comp Real.log (fun t => 1 - t) T (hg := (Matrix.finite_real_spectrum.image _).continuousOn _)
        (hf := hc _)
    rw [hcomp, Algebra.algebraMap_eq_smul_one, hcs]

end
