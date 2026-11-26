-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_contDiff_M__e4c66d3c2429
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:53:00.970969+00:00
-- url     : https://prove2.me/submissions/38edf304-0d24-4e39-8097-22ec9f8f2528

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Regularity_contDiff_p__7eb957c067a9
import Theorems.Thm_FriedCrossing_Derived_two_add_one_le_three

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A) (i j : Fin 2) :
    ContDiff ℝ 2 fun q : ℝ × ℝ => Mτ M q.1 q.2 i j :=
  contDiff_pτ (f := fun θ τ => M θ τ i j) two_add_one_le_three (h.deg1 i j)
end FriedCrossing.Derived
