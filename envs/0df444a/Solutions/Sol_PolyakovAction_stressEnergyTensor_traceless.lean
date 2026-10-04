-- Prove2me | solution 1 for PolyakovAction.stressEnergyTensor_traceless
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-03T13:38:09.589884+00:00
-- url     : https://prove2.me/submissions/c708555d-8c3c-4624-9cb5-7a3f9339da67

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open Matrix
open scoped BigOperators

theorem solution {D : ℕ} (T : ℝ)
    (g : PolyakovAction.Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : PolyakovAction.Worldsheet → Matrix (Fin 2) (Fin 2) ℝ)
    (X : PolyakovAction.Worldsheet → PolyakovAction.Spacetime D)
    (σ : PolyakovAction.Worldsheet) (hsymm : (h σ)ᵀ = h σ) (hdet : (h σ).det ≠ 0) :
    ∑ a, ∑ b, (h σ)⁻¹ a b * PolyakovAction.stressEnergyTensor T g h X σ a b = 0 := by
  set H : Matrix (Fin 2) (Fin 2) ℝ := h σ
  set Gm : Matrix (Fin 2) (Fin 2) ℝ := PolyakovAction.inducedMetric g X σ
  let tr : ℝ := ∑ c : Fin 2, ∑ d : Fin 2, H⁻¹ c d * Gm c d
  have hunit : IsUnit H.det := (isUnit_iff_ne_zero).mpr hdet
  have hsym : ∀ a b : Fin 2, H a b = H b a := by
    intro a b
    have hba : Hᵀ a b = H b a := by simp [Matrix.transpose_apply]
    rw [hsymm] at hba
    exact hba
  have hcontract : ∑ a : Fin 2, ∑ b : Fin 2, H⁻¹ a b * H a b = (2 : ℝ) := by
    have hrewrite :
        ∑ a : Fin 2, ∑ b : Fin 2, H⁻¹ a b * H a b =
          ∑ a : Fin 2, (H⁻¹ * H) a a := by
      refine Finset.sum_congr rfl ?_
      intro a _
      simp only [Matrix.mul_apply]
      refine Finset.sum_congr rfl ?_
      intro b _
      rw [hsym a b]
    rw [hrewrite]
    have htrace : ∑ a : Fin 2, (H⁻¹ * H) a a = Matrix.trace (H⁻¹ * H) := by
      simp [Matrix.trace, Matrix.diag_apply]
    rw [htrace, H.nonsing_inv_mul hunit, Matrix.trace_one]
    simp [Fintype.card_fin]
  have hentry :
      ∀ a b : Fin 2,
        PolyakovAction.stressEnergyTensor T g h X σ a b =
          T * (Gm a b - (1 / 2) * H a b * tr) := by
    intro a b
    simp [PolyakovAction.stressEnergyTensor, Matrix.of_apply, H, Gm, tr]
  simp_rw [hentry]
  have hpull :
      ∀ a b : Fin 2,
        H⁻¹ a b * (T * (Gm a b - (1 / 2) * H a b * tr)) =
          T * (H⁻¹ a b * Gm a b - (1 / 2) * tr * (H⁻¹ a b * H a b)) := by
    intro a b
    ring
  simp_rw [hpull, ← Finset.mul_sum]
  have hsplit :
      (∑ a : Fin 2, ∑ b : Fin 2,
          (H⁻¹ a b * Gm a b - (1 / 2) * tr * (H⁻¹ a b * H a b))) =
        tr - (1 / 2) * tr * ∑ a : Fin 2, ∑ b : Fin 2, H⁻¹ a b * H a b := by
    have hA :
        ∑ a : Fin 2, ∑ b : Fin 2, (H⁻¹ a b * Gm a b - (1 / 2) * tr * (H⁻¹ a b * H a b)) =
          (∑ a : Fin 2, ∑ b : Fin 2, H⁻¹ a b * Gm a b) -
            ∑ a : Fin 2, ∑ b : Fin 2, (1 / 2) * tr * (H⁻¹ a b * H a b) := by
      simp_rw [Finset.sum_sub_distrib]
    rw [hA]
    have htr : ∑ a : Fin 2, ∑ b : Fin 2, H⁻¹ a b * Gm a b = tr := by
      simp [tr]
    rw [htr]
    have hB :
        ∑ a : Fin 2, ∑ b : Fin 2, (1 / 2) * tr * (H⁻¹ a b * H a b) =
          (1 / 2) * tr * ∑ a : Fin 2, ∑ b : Fin 2, H⁻¹ a b * H a b := by
      simp_rw [← Finset.mul_sum]
    rw [hB]
  rw [hsplit, hcontract]
  ring
