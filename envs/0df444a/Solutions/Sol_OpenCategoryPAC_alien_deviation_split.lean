-- Prove2me | solution 1 for OpenCategoryPAC.alien_deviation_split
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T11:38:49.565646+00:00
-- url     : https://prove2.me/submissions/2a6c26fd-f620-4bd5-9e14-58a68db3433b

import Mathlib
import Definitions.Def_OpenCategoryPAC_Basic
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Filter Topology
namespace OpenCategoryPAC

lemma ads_mix (μ0 μa : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1) [IsProbabilityMeasure (mixture α μ0 μa)] (t : ℝ) :
    cdf (mixture α μ0 μa) t = (1 - α) * cdf μ0 t + α * cdf μa t := by
  rw [cdf_eq_real, cdf_eq_real, cdf_eq_real]
  simp only [mixture, measureReal_def, Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  rw [ENNReal.toReal_add (by simp [ENNReal.mul_eq_top]) (by simp [ENNReal.mul_eq_top]),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by linarith),
    ENNReal.toReal_ofReal hα0.le]

lemma ads_empCDF_mem {n : ℕ} (x : Fin n → ℝ) (t : ℝ) : 0 ≤ empCDF x t ∧ empCDF x t ≤ 1 := by
  unfold empCDF
  refine ⟨by positivity, ?_⟩
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · rw [div_le_one (by exact_mod_cast h)]
    have := Finset.card_filter_le (Finset.univ : Finset (Fin n)) (fun i => x i ≤ t)
    simp at this; exact_mod_cast this

lemma ads_le (F G : ℝ → ℝ) (hF : ∀ t, 0 ≤ F t ∧ F t ≤ 1) (hG : ∀ t, 0 ≤ G t ∧ G t ≤ 1) (t : ℝ) :
    |F t - G t| ≤ supDev F G := by
  unfold supDev
  refine le_ciSup (f := fun t => |F t - G t|) ⟨1, ?_⟩ t
  rintro _ ⟨s, rfl⟩
  have := hF s; have := hG s
  simp only; rw [abs_le]; constructor <;> linarith

theorem alien_deviation_split (μ0 μa μm : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μm] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hm : μm = mixture α μ0 μa) (ε : ℝ) (hε : 0 < ε) {n : ℕ} (x y : Fin n → ℝ)
    (h : ε < supDev (alienCDFEst α x y) (cdf μa)) :
    α / (2 - α) * ε < supDev (empCDF y) (cdf μm) ∨
      α / (2 - α) * ε < supDev (empCDF x) (cdf μ0) := by
  by_contra hc
  push_neg at hc
  obtain ⟨h1, h2⟩ := hc
  have hcdf : ∀ (ν : Measure ℝ) [IsProbabilityMeasure ν] (t : ℝ), 0 ≤ cdf ν t ∧ cdf ν t ≤ 1 :=
    fun ν _ t => ⟨cdf_nonneg ν t, cdf_le_one ν t⟩
  have key : ∀ t, |alienCDFEst α x y t - cdf μa t| ≤ ε := by
    intro t
    have e1 := ads_le (empCDF y) (cdf μm) (ads_empCDF_mem y) (hcdf μm) t
    have e2 := ads_le (empCDF x) (cdf μ0) (ads_empCDF_mem x) (hcdf μ0) t
    have hmix : cdf μm t = (1 - α) * cdf μ0 t + α * cdf μa t := by
      subst hm; exact ads_mix μ0 μa α hα0 hα1 t
    have hrw : alienCDFEst α x y t - cdf μa t =
        ((empCDF y t - cdf μm t) - (1 - α) * (empCDF x t - cdf μ0 t)) / α := by
      unfold alienCDFEst alienCDF; rw [hmix]; field_simp; ring
    rw [hrw, abs_div, abs_of_pos hα0, div_le_iff₀ hα0]
    have h2a : 0 < 2 - α := by linarith
    have hb : |empCDF y t - cdf μm t| + (1 - α) * |empCDF x t - cdf μ0 t| ≤ α * ε := by
      have q1 : |empCDF y t - cdf μm t| ≤ α / (2 - α) * ε := e1.trans h1
      have q2 : (1 - α) * |empCDF x t - cdf μ0 t| ≤ (1 - α) * (α / (2 - α) * ε) :=
        mul_le_mul_of_nonneg_left (e2.trans h2) (by linarith)
      have : α / (2 - α) * ε + (1 - α) * (α / (2 - α) * ε) = α * ε := by
        field_simp; ring
      linarith
    calc |empCDF y t - cdf μm t - (1 - α) * (empCDF x t - cdf μ0 t)|
        ≤ |empCDF y t - cdf μm t| + |(1 - α) * (empCDF x t - cdf μ0 t)| := abs_sub _ _
      _ = |empCDF y t - cdf μm t| + (1 - α) * |empCDF x t - cdf μ0 t| := by
          rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ 1 - α)]
      _ ≤ α * ε := hb
      _ = ε * α := mul_comm _ _
  have : supDev (alienCDFEst α x y) (cdf μa) ≤ ε := ciSup_le key
  linarith

end OpenCategoryPAC
open OpenCategoryPAC in
theorem solution (μ0 μa μm : Measure ℝ) [IsProbabilityMeasure μ0]
    [IsProbabilityMeasure μa] [IsProbabilityMeasure μm] (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hm : μm = mixture α μ0 μa) (ε : ℝ) (hε : 0 < ε) {n : ℕ} (x y : Fin n → ℝ)
    (h : ε < supDev (alienCDFEst α x y) (cdf μa)) :
    α / (2 - α) * ε < supDev (empCDF y) (cdf μm) ∨
      α / (2 - α) * ε < supDev (empCDF x) (cdf μ0) :=
  alien_deviation_split μ0 μa μm α hα0 hα1 hm ε hε x y h
