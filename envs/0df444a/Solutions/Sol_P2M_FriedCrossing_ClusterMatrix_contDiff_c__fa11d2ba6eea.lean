-- Prove2me | solution 1 for P2M_FriedCrossing_ClusterMatrix_contDiff_c__fa11d2ba6eea
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:03:32.04128+00:00
-- url     : https://prove2.me/submissions/a7f76ff8-4b19-4ac1-95bb-d8fbdd2b15ae

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_ClusterMatrix_contDiff_charpoly_coeff

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {k : WithTop ℕ∞}
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution {A : E → Matrix (Fin 4) (Fin 4) ℝ}
    (h : ∀ i j, ContDiff ℝ k fun x => A x i j) : ContDiff ℝ k fun x => c₂ (A x) :=
  contDiff_charpoly_coeff h 2 (by norm_num)
end FriedCrossing.ClusterMatrix
