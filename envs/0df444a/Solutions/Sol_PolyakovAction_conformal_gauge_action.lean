-- Prove2me | solution 1 for PolyakovAction.conformal_gauge_action
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T05:35:52.03739+00:00
-- url     : https://prove2.me/submissions/774a2266-67a7-40a0-9bd2-0b74af6aa0c1

import Mathlib
import Definitions.Def_PolyakovAction_Defs

open MeasureTheory Filter Asymptotics
open scoped Matrix Topology

namespace PolyakovAction

lemma eta2_mul_self_61052a09 : minkowskiMetric 2 * minkowskiMetric 2 = 1 := by
  unfold minkowskiMetric
  rw [Matrix.diagonal_mul_diagonal]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.one_apply]

lemma eta2_inv_61052a09 : (minkowskiMetric 2)⁻¹ = minkowskiMetric 2 :=
  Matrix.inv_eq_left_inv eta2_mul_self_61052a09

lemma eta2_det_61052a09 : (minkowskiMetric 2).det = -1 := by
  unfold minkowskiMetric
  rw [Matrix.det_diagonal, Fin.prod_univ_two]
  norm_num

lemma lagr_61052a09 {D : ℕ} (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (X : Worldsheet → Spacetime D) (σ : Worldsheet) :
    polyakovLagrangian g (fun _ => minkowskiMetric 2) X σ
      = inducedMetric g X σ 0 0 - inducedMetric g X σ 1 1 := by
  unfold polyakovLagrangian
  rw [eta2_inv_61052a09, eta2_det_61052a09]
  simp only [neg_neg, Real.sqrt_one, one_mul, Fin.sum_univ_two]
  simp [minkowskiMetric, Matrix.diagonal_apply]
  ring

end PolyakovAction

open PolyakovAction in
theorem solution {D : ℕ} (T : ℝ) (g : Spacetime D → Matrix (Fin D) (Fin D) ℝ)
    (X : Worldsheet → Spacetime D) (U : Set Worldsheet) :
    polyakovAction T g (fun _ => minkowskiMetric 2) X U
      = T / 2 * ∫ σ in U, (inducedMetric g X σ 0 0 - inducedMetric g X σ 1 1) := by
  unfold polyakovAction
  simp_rw [lagr_61052a09]
