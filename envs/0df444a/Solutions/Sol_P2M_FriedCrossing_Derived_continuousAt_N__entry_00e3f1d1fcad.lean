-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_continuousAt_N__entry_00e3f1d1fcad
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:04:55.612329+00:00
-- url     : https://prove2.me/submissions/d15267ef-d0e5-41cf-8765-b8c2d8255d3c

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_HQuot_continuousAt_hq__329f1ab477c4
import Theorems.Thm_FriedCrossing_Derived_hasDerivAt_M
import Theorems.Thm_P2M_FriedCrossing_Derived_hasDerivAt_M__92e08b1bff5c
import Theorems.Thm_P2M_FriedCrossing_Derived_continuousAt_M___1cabb0862b68

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
    ContinuousAt (fun q : ℝ × ℝ => Nτ M q.1 q.2 i j) (0, 0) :=
  continuousAt_hq' (F := fun θ t => M θ t i j) (F' := fun θ t => Mτ M θ t i j)
    (F'' := fun θ t => Mττ M θ t i j) (fun θ t => hasDerivAt_M h θ t i j)
    (fun θ t => hasDerivAt_Mτ h θ t i j) (continuousAt_Mττ h i j)
end FriedCrossing.Derived
