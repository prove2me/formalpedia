-- Prove2me | solution 1 for SpikedWishart.FixedDim.eq_29
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:13:14.71018+00:00
-- url     : https://prove2.me/submissions/6245bb4d-62b3-4f30-ad05-2f549561bd38

import Mathlib
import Definitions.Def_SpikedWishart_FixedDim_GUE

set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set SpikedWishart.FixedDim

theorem pi_int (g : ℝ → ℝ) (s : Set ℝ) :
    ∫ ξ in Set.pi univ (fun _ : Fin 1 => s), g (ξ 0) = ∫ t in s, g t := by
  have hmp := volume_preserving_funUnique (Fin 1) ℝ
  have h := hmp.setIntegral_preimage_emb (MeasurableEquiv.funUnique (Fin 1) ℝ).measurableEmbedding g s
  have hset : (MeasurableEquiv.funUnique (Fin 1) ℝ) ⁻¹' s = Set.pi univ (fun _ : Fin 1 => s) := by
    ext ξ
    simp [MeasurableEquiv.funUnique, Set.mem_pi]
  rw [hset] at h
  convert h using 3 <;> first | rfl | skip

theorem vand_one (ξ : Fin 1 → ℝ) : vandSq ξ = 1 := by
  simp [vandSq]

theorem solution (x : ℝ) : G 1 x = (gaussianReal 0 1).real (Iic x) := by
  have h1 : ∀ ξ : Fin 1 → ℝ, vandSq ξ * ∏ i, Real.exp (-(ξ i) ^ 2 / 2) = Real.exp (-(ξ 0) ^ 2 / 2) := by
    intro ξ; simp [vand_one]
  have hZ : Z 1 = Real.sqrt (2 * Real.pi) := by
    unfold Z
    simp only [h1]
    have := pi_int (fun t => Real.exp (-t ^ 2 / 2)) Set.univ
    rw [Set.pi_univ, setIntegral_univ, setIntegral_univ] at this
    rw [this]
    have h2 : ∀ t : ℝ, Real.exp (-t ^ 2 / 2) = Real.exp (-(1 / 2) * t ^ 2) := by
      intro t; congr 1; ring
    simp only [h2]
    rw [integral_gaussian]
    congr 1
    field_simp
  have hG : G 1 x = (Real.sqrt (2 * Real.pi))⁻¹ * ∫ t in Iic x, Real.exp (-t ^ 2 / 2) := by
    unfold G
    simp only [h1]
    rw [hZ, pi_int (fun t => Real.exp (-t ^ 2 / 2)) (Iic x)]
  rw [hG, measureReal_def, gaussianReal_apply_eq_integral 0 one_ne_zero (Iic x)]
  rw [ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Iic fun t _ => gaussianPDFReal_nonneg _ _ _)]
  have h3 : ∀ t : ℝ, gaussianPDFReal 0 1 t = (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-t ^ 2 / 2) := by
    intro t
    rw [gaussianPDFReal_def]
    simp
  simp only [h3]
  rw [integral_const_mul]
