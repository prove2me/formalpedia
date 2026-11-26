-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_finrank_resZero__f29bef30b26c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:00:25.82581+00:00
-- url     : https://prove2.me/submissions/b5359b64-95f6-4866-9a4c-e144a74ba7ab

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
namespace FriedCrossing.Derived
theorem _root_.solution (M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ τ : ℝ) :
    Module.finrank ℝ (resZero₁ M θ τ) = (M θ τ).charpoly.rootMultiplicity 0 := by
  rw [resZero₁, LinearMap.finrank_maxGenEigenspace_eq, Matrix.charpoly_toLin']
end FriedCrossing.Derived
