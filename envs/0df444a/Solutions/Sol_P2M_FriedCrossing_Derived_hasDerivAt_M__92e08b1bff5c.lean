-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_hasDerivAt_M__92e08b1bff5c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:55:11.509737+00:00
-- url     : https://prove2.me/submissions/a9899e1b-f055-4ec2-9ca7-42207d246946

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Regularity_hasDerivAt_p__ad8317175eea
import Theorems.Thm_FriedCrossing_Regularity_differentiable_of_contDiff
import Theorems.Thm_FriedCrossing_Derived_one_add_one_le_two
import Theorems.Thm_P2M_FriedCrossing_Derived_contDiff_M__e4c66d3c2429

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A) (θ τ : ℝ) (i j : Fin 2) :
    HasDerivAt (fun t => Mτ M θ t i j) (Mττ M θ τ i j) τ :=
  hasDerivAt_pτ (f := fun θ τ => Mτ M θ τ i j)
    (differentiable_of_contDiff (f := fun θ τ => Mτ M θ τ i j) one_add_one_le_two
      (contDiff_Mτ h i j)) θ τ
end FriedCrossing.Derived
