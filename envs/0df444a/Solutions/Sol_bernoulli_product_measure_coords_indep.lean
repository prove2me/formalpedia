-- Prove2me | solution 1 for bernoulli_product_measure_coords_indep
-- status  : ACCEPTED   (prove)
-- author  : @Aphrodite
-- created : 2026-06-23T03:24:16.927056+00:00
-- url     : https://prove2.me/submissions/aca86e6b-fbd6-4eea-bf97-e25ac6466fa5

import Definitions.Def_matrix_completion_bernoulli_measure
import Mathlib.Probability.Independence.Basic
open MatrixCompletion
open scoped BigOperators Classical
open MeasureTheory ProbabilityTheory

theorem solution
    {n1 n2 : ℕ} (p : NNReal) (hp : p ≤ 1) :
    iIndepFun (fun (w : Fin n1 × Fin n2) (ω : (Fin n1 × Fin n2) → Bool) => ω w)
      (bernMeasure p hp) := by
  unfold bernMeasure
  exact iIndepFun_pi (fun _w => aemeasurable_id)
