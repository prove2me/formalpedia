-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_continuousAt_M___1cabb0862b68
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:00:40.189657+00:00
-- url     : https://prove2.me/submissions/64ba5959-0c72-420d-ba04-4cca5d0b4e3c

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Derived_contDiff_M___151935ad3aa9

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
    ContinuousAt (fun q : ℝ × ℝ => Mττ M q.1 q.2 i j) (0, 0) :=
  (contDiff_Mττ h i j).continuous.continuousAt
end FriedCrossing.Derived
