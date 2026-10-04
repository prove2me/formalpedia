-- Prove2me | solution 1 for PolyakovAction.polyakov_eq_nambuGoto
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T09:54:21.170211+00:00
-- url     : https://prove2.me/submissions/14c05862-e829-4c80-8bea-0f490b979408

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

set_option autoImplicit false

lemma polyakov_det_aux_1400e518 (G H : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (hG : ∀ a b, G a b = 1 / 2 * H a b * s) :
    G.det = 1 / 4 * H.det * s ^ 2 := by
  rw [Matrix.det_fin_two G, Matrix.det_fin_two H, hG 0 0, hG 0 1, hG 1 0, hG 1 1]
  ring

open PolyakovAction in
lemma polyakov_pointwise_1400e518 {D : ℕ} (T : ℝ) (hT : T ≠ 0)
    (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (σ : Worldsheet) (heom : stressEnergyTensor T g h X σ = 0)
    (hpos : 0 ≤ ∑ c, ∑ d, (h σ)⁻¹ c d * inducedMetric g X σ c d) :
    polyakovLagrangian g h X σ = 2 * Real.sqrt (-(inducedMetric g X σ).det) := by
  set s := ∑ c, ∑ d, (h σ)⁻¹ c d * inducedMetric g X σ c d with hs
  have hdet : (inducedMetric g X σ).det = 1 / 4 * (h σ).det * s ^ 2 := by
    apply polyakov_det_aux_1400e518
    intro a b
    have e := congrFun (congrFun heom a) b
    simp only [stressEnergyTensor, Matrix.of_apply, Matrix.zero_apply] at e
    rcases mul_eq_zero.mp e with h0 | h0
    · exact absurd h0 hT
    · rw [← hs] at h0
      linarith
  have hneg : -(inducedMetric g X σ).det = (s / 2) ^ 2 * (-(h σ).det) := by
    rw [hdet]; ring
  rw [hneg, Real.sqrt_mul (sq_nonneg (s / 2)), Real.sqrt_sq (div_nonneg hpos two_pos.le)]
  simp only [polyakovLagrangian]
  rw [← hs]
  ring

open PolyakovAction in
theorem solution {D : ℕ} (T : ℝ) (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (U : Set Worldsheet) (hU : MeasurableSet U)
    (heom : ∀ σ ∈ U, stressEnergyTensor T g h X σ = 0)
    (hpos : ∀ σ ∈ U, 0 ≤ ∑ c, ∑ d, (h σ)⁻¹ c d * inducedMetric g X σ c d) :
    polyakovAction T g h X U = nambuGotoAction T g X U := by
  by_cases hT : T = 0
  · subst hT
    simp [polyakovAction, nambuGotoAction]
  · unfold polyakovAction nambuGotoAction
    rw [setIntegral_congr_fun hU (fun σ hσ =>
      polyakov_pointwise_1400e518 T hT g h X σ (heom σ hσ) (hpos σ hσ))]
    rw [integral_const_mul]
    ring
