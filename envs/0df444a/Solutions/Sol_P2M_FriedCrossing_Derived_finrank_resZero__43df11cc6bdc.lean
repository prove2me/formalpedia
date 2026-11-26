-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_finrank_resZero__43df11cc6bdc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:00:28.752134+00:00
-- url     : https://prove2.me/submissions/e87485f8-0f03-4cb1-9ca6-d0d171aba446

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
namespace FriedCrossing.Derived
theorem _root_.solution (A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ) (θ τ : ℝ) :
    Module.finrank ℝ (resZero₂ A θ τ) = (A θ τ).charpoly.rootMultiplicity 0 := by
  rw [resZero₂, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']
end FriedCrossing.Derived
