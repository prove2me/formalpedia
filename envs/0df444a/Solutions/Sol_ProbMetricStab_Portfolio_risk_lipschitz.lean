-- Prove2me | solution 1 for ProbMetricStab.Portfolio.risk_lipschitz
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T02:31:59.544656+00:00
-- url     : https://prove2.me/submissions/78c10665-f8a5-4c7f-a17a-d393374d83b8

import Mathlib
import Definitions.Def_ProbMetricStab_Portfolio_Setting
import Theorems.Thm_ProbMetricStab_Portfolio_abs_rpow_sub_le
import Theorems.Thm_ProbMetricStab_Portfolio_lemma_5_1_a

open MeasureTheory
open scoped ENNReal
open ProbMetricStab.Portfolio

theorem solution {s : ℕ} (α α' : ℝ) (hα1 : 1 < α) (hα2 : α < 2) (hα'1 : 1 < α')
    (hα'2 : α' < 2) (Γ Γ' : Measure (Rs s)) (hΓ : IsSpectral Γ) (hΓ' : IsSpectral Γ')
    (x : Rs s) (hx : x ∈ simplex s) :
    ENNReal.ofReal |risk α Γ x - risk α' Γ' x|
      ≤ ENNReal.ofReal α * zeta1 Γ Γ' + ENNReal.ofReal (Real.exp (-1) * |α - α'|) := by
  haveI := hΓ.1
  haveI := hΓ'.1
  have hα0 : 0 < α := by linarith
  -- norm of a simplex point is at most 1
  have hxn : ‖x‖ ≤ 1 := by
    have hsq : ‖x‖ ^ 2 ≤ 1 := by
      rw [EuclideanSpace.norm_sq_eq]
      have hle : ∀ i, x i ≤ 1 := by
        intro i
        rw [← hx.2]
        exact Finset.single_le_sum (fun j _ => hx.1 j) (Finset.mem_univ i)
      calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ i, x i := by
            apply Finset.sum_le_sum
            intro i _
            rw [Real.norm_eq_abs, sq_abs, sq]
            nlinarith [hx.1 i, hle i]
        _ = 1 := hx.2
    nlinarith [norm_nonneg x]
  have hin : ∀ ξ ∈ unitSphere s, (inner ℝ x ξ : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by
    intro ξ hξ
    have hξn : ‖ξ‖ = 1 := by simpa [unitSphere] using hξ
    have := abs_real_inner_le_norm x ξ
    rw [hξn, mul_one] at this
    exact abs_le.mp (this.trans hxn)
  have hcont : ∀ β : ℝ, 0 < β → Continuous (fun ξ : Rs s => f0 β ξ x) := by
    intro β hβ
    unfold f0
    exact ((continuous_const.inner continuous_id).abs).rpow_const (fun _ => Or.inr hβ.le)
  have hcpt : IsCompact (unitSphere s) := isCompact_sphere 0 1
  have hint : ∀ (β : ℝ), 0 < β → ∀ (μ : Measure (Rs s)) [IsFiniteMeasure μ],
      IntegrableOn (fun ξ : Rs s => f0 β ξ x) (unitSphere s) μ :=
    fun β hβ μ _ => (hcont β hβ).continuousOn.integrableOn_compact hcpt
  -- the ζ₁ part
  set g : Rs s → ℝ := fun ξ => α⁻¹ * f0 α ξ x with hg
  have hgL : g ∈ lipTest s := by
    show LipschitzOnWith 1 g (unitSphere s)
    apply LipschitzOnWith.of_dist_le_mul
    intro ξ hξ ξ' hξ'
    have h := (lemma_5_1_a α hα1 hα2).2 x hx x hx ξ hξ ξ' hξ'
    rw [sub_self, norm_zero, add_zero] at h
    simp only [hg, Real.dist_eq, NNReal.coe_one, one_mul]
    rw [← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hα0), dist_eq_norm]
    rw [inv_mul_le_iff₀ hα0]
    exact h
  have hζ : ENNReal.ofReal |(∫ ξ in unitSphere s, g ξ ∂Γ) - ∫ ξ in unitSphere s, g ξ ∂Γ'|
      ≤ zeta1 Γ Γ' := by
    unfold zeta1
    exact le_iSup₂_of_le (f := fun f (_ : f ∈ lipTest s) =>
      ENNReal.ofReal |(∫ ξ in unitSphere s, f ξ ∂Γ) - ∫ ξ in unitSphere s, f ξ ∂Γ'|) g hgL le_rfl
  have hgint : ∀ μ : Measure (Rs s), (∫ ξ in unitSphere s, g ξ ∂μ)
      = α⁻¹ * ∫ ξ in unitSphere s, f0 α ξ x ∂μ := fun μ => integral_const_mul _ _
  set A := (∫ ξ in unitSphere s, f0 α ξ x ∂Γ) - ∫ ξ in unitSphere s, f0 α ξ x ∂Γ' with hA
  set B := ∫ ξ in unitSphere s, (f0 α ξ x - f0 α' ξ x) ∂Γ' with hB
  have hsplit : risk α Γ x - risk α' Γ' x = A + B := by
    simp only [risk, hA, hB]
    rw [integral_sub (hint α hα0 Γ') (hint α' (by linarith) Γ')]
    ring
  have hAeq : |A| = α * |(∫ ξ in unitSphere s, g ξ ∂Γ) - ∫ ξ in unitSphere s, g ξ ∂Γ'| := by
    rw [hgint, hgint, ← mul_sub, abs_mul, abs_of_pos (inv_pos.mpr hα0), ← mul_assoc,
      mul_inv_cancel₀ hα0.ne', one_mul]
  have hBle : |B| ≤ Real.exp (-1) * |α - α'| := by
    have h := norm_setIntegral_le_of_norm_le_const (μ := Γ') (s := unitSphere s)
      (f := fun ξ => f0 α ξ x - f0 α' ξ x) (C := Real.exp (-1) * |α - α'|)
      (measure_lt_top _ _) (by
        intro ξ hξ
        rw [Real.norm_eq_abs]
        exact abs_rpow_sub_le α α' hα1 hα2 hα'1 hα'2 _ (hin ξ hξ))
    rw [Real.norm_eq_abs] at h
    refine h.trans ?_
    have hC : 0 ≤ Real.exp (-1) * |α - α'| := mul_nonneg (Real.exp_pos _).le (abs_nonneg _)
    have hm : Γ'.real (unitSphere s) ≤ 1 := measureReal_le_one
    nlinarith
  rw [hsplit]
  calc ENNReal.ofReal |A + B| ≤ ENNReal.ofReal (|A| + |B|) :=
        ENNReal.ofReal_le_ofReal (abs_add_le A B)
    _ = ENNReal.ofReal |A| + ENNReal.ofReal |B| :=
        ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)
    _ ≤ ENNReal.ofReal α * zeta1 Γ Γ' + ENNReal.ofReal (Real.exp (-1) * |α - α'|) := by
        gcongr
        rw [hAeq, ENNReal.ofReal_mul hα0.le]
        gcongr
