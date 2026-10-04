-- Prove2me | solution 1 for PolyakovAction.weyl_invariance
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:42:04.66559+00:00
-- url     : https://prove2.me/submissions/173df24d-3988-41b3-abbe-3e9d016969de

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

set_option autoImplicit false

theorem PolyakovAction_weyl_pointwise_189e7717 (c : ℝ) (hc : 0 < c)
    (H G : Matrix (Fin 2) (Fin 2) ℝ) :
    Real.sqrt (-(c • H).det) * ∑ a, ∑ b, (c • H)⁻¹ a b * G a b
      = Real.sqrt (-H.det) * ∑ a, ∑ b, H⁻¹ a b * G a b := by
  have hdet : (c • H).det = c ^ 2 * H.det := by
    rw [Matrix.det_smul]; simp [Fintype.card_fin]
  have hsq : Real.sqrt (-(c • H).det) = c * Real.sqrt (-H.det) := by
    rw [hdet, show -(c ^ 2 * H.det) = c ^ 2 * (-H.det) by ring,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  rw [hsq]
  by_cases hd : H.det = 0
  · rw [hd]; simp
  · have hu : IsUnit H.det := isUnit_iff_ne_zero.mpr hd
    have hinv : (c • H)⁻¹ = c⁻¹ • H⁻¹ := by
      have := Matrix.inv_smul' (A := H) (k := Units.mk0 c hc.ne') (h := hu)
      simpa [Units.smul_def] using this
    rw [hinv]
    simp only [Matrix.smul_apply, smul_eq_mul, Fin.sum_univ_two]
    field_simp

open PolyakovAction in
theorem solution {D : ℕ} (T : ℝ) (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (Λ : Worldsheet → ℝ) (hΛ : ∀ σ, 0 < Λ σ) (U : Set Worldsheet) :
    polyakovAction T g (fun σ => Λ σ • h σ) X U = polyakovAction T g h X U := by
  unfold polyakovAction
  congr 2
  funext σ
  unfold polyakovLagrangian
  exact PolyakovAction_weyl_pointwise_189e7717 (Λ σ) (hΛ σ) (h σ) (inducedMetric g X σ)
