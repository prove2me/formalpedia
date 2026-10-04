-- Prove2me | solution 1 for PolyakovAction.det_inducedMetric_of_eom
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T06:16:35.969636+00:00
-- url     : https://prove2.me/submissions/9a2e4689-40bc-4632-8e5a-b86155483379

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

set_option autoImplicit false

lemma polyakov_det_aux_4a007aa3 (G H : Matrix (Fin 2) (Fin 2) ℝ) (s : ℝ)
    (hG : ∀ a b, G a b = 1 / 2 * H a b * s) :
    G.det = 1 / 4 * H.det * s ^ 2 := by
  rw [Matrix.det_fin_two G, Matrix.det_fin_two H, hG 0 0, hG 0 1, hG 1 0, hG 1 1]
  ring

open PolyakovAction in
theorem solution {D : ℕ} (T : ℝ) (hT : T ≠ 0)
    (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (h : Worldsheet → Matrix (Fin 2) (Fin 2) ℝ) (X : Worldsheet → Spacetime D)
    (σ : Worldsheet) (heom : stressEnergyTensor T g h X σ = 0) :
    (inducedMetric g X σ).det
      = 1 / 4 * (h σ).det * (∑ c, ∑ d, (h σ)⁻¹ c d * inducedMetric g X σ c d) ^ 2 := by
  apply polyakov_det_aux_4a007aa3
  intro a b
  have e := congrFun (congrFun heom a) b
  simp only [stressEnergyTensor, Matrix.of_apply, Matrix.zero_apply] at e
  rcases mul_eq_zero.mp e with h0 | h0
  · exact absurd h0 hT
  · linarith
