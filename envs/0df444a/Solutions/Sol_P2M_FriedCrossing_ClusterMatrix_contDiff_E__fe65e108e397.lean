-- Prove2me | solution 1 for P2M_FriedCrossing_ClusterMatrix_contDiff_E__fe65e108e397
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:05:48.532282+00:00
-- url     : https://prove2.me/submissions/e9800b45-09f9-46a9-9f26-c6625a09c81b

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_contDiff_c__fa11d2ba6eea
import Theorems.Thm_FriedCrossing_ClusterMatrix_contDiff_trace_fin_two
import Theorems.Thm_FriedCrossing_ClusterMatrix_contDiff_det_fin_two
import Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_contDiff_E__fcc4cec339ab

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution {A : E → Matrix (Fin 4) (Fin 4) ℝ} {M : E → Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ i j, ContDiff ℝ k fun x => A x i j) (hM : ∀ i j, ContDiff ℝ k fun x => M x i j) :
    ContDiff ℝ k fun x => E₂ (A x) (M x) :=
  ((contDiff_c₂ hA).sub (contDiff_det_fin_two hM)).sub
    ((contDiff_trace_fin_two hM).mul (contDiff_E₁ hA hM))
end FriedCrossing.ClusterMatrix
