-- Prove2me | solution 1 for P2M_FriedCrossing_ClusterMatrix_E__eq_1169bea58b61
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:59:21.721727+00:00
-- url     : https://prove2.me/submissions/09b5556d-949d-4ff1-8e88-72ea7b6b5ce6

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.ClusterMatrix
namespace FriedCrossing.ClusterMatrix
theorem _root_.solution (A : Matrix (Fin 4) (Fin 4) ℝ) (M : Matrix (Fin 2) (Fin 2) ℝ) {scl snc : ℝ}
    (hs : scl + snc = M.trace) (hp : scl * snc = M.det) :
    E₂ A M = PureZeros.e₂of (c₁ A) (c₂ A) scl snc := by
  unfold E₂ E₁ PureZeros.e₂of PureZeros.e₁of; rw [← hs, ← hp]; ring
end FriedCrossing.ClusterMatrix
