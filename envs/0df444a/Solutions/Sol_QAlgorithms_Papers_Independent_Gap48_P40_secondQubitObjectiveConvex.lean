-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Gap48.P40.secondQubitObjectiveConvex
-- status  : ACCEPTED   (prove)
-- author  : @Alien60
-- created : 2026-10-27T20:59:40.294312+00:00
-- url     : https://prove2.me/submissions/3838f3a1-4e07-4ff5-855b-e33effe29a40

import Definitions.Def_QAlgorithms_Papers_Independent_Gap48_P40
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_qubitObjectiveTwo_eq_closedForm
import Theorems.Thm_QAlgorithms_Papers_Independent_Gap48_P40_qubitObjectiveTwo_closedForm_convex

noncomputable section

open scoped Matrix ComplexConjugate ComplexOrder Topology Matrix.Norms.L2Operator

open Filter MeasureTheory Asymptotics

open QAlgorithms

open QAlgorithms.Papers.Independent.Dependency50.P21 (relativeEntropy)

open QAlgorithms.Papers.Independent.Information100.P50 (IsUINorm)

open QAlgorithms.Papers.Independent.Information100.P56 (entropy)

open QAlgorithms.Papers.Independent.Information100.P60 (copies)

open QAlgorithms.Papers.Independent.Information100.P44 (Mat)

open QAlgorithms.Papers.Independent.Gap48.P40

theorem solution (beta T : ℝ) (hbeta : 0 < beta ∧ beta ≤ 1 / 2)
    (hT : beta < T ∧ T ≤ 1 - beta) :
    ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) (qubitObjectiveTwo beta T) :=
  (qubitObjectiveTwo_closedForm_convex beta T hbeta hT).congr fun t ht =>
    (qubitObjectiveTwo_eq_closedForm beta T t hbeta hT ht).symm


end
