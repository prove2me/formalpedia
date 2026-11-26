-- Prove2me | solution 1 for P2M_FriedCrossing_ClusterMatrix_contDiff_E__fcc4cec339ab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:04:28.989935+00:00
-- url     : https://prove2.me/submissions/dc3c2e9f-8d04-41d6-9352-7241c569c647

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_contDiff_c__cd886b5105a5
import Theorems.Thm_FriedCrossing_ClusterMatrix_contDiff_trace_fin_two

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution {A : E → Matrix (Fin 4) (Fin 4) ℝ} {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContDiff ℝ k fun x => A x i j) (hM : ∀ i j, ContDiff ℝ k fun x => M x i j) :
    ContDiff ℝ k fun x => E₁ (A x) (M x) :=
  (contDiff_c₁ hA).sub (contDiff_trace_fin_two hM)
end FriedCrossing.ClusterMatrix
