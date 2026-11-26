-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_continuousAt_a__6cdfbca45661
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:07:09.096258+00:00
-- url     : https://prove2.me/submissions/9af4c041-d97f-402b-a999-c2ef4c58eca2

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_Derived_continuousAt_N__entry_00e3f1d1fcad

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A) : ContinuousAt (Function.uncurry (aτ M)) (0, 0) := by
  have : Function.uncurry (aτ M) = fun q : ℝ × ℝ => Nτ M q.1 q.2 0 0 + Nτ M q.1 q.2 1 1 := by
    funext q; simp [Function.uncurry, aτ, Matrix.trace_fin_two]
  rw [this]
  exact (continuousAt_Nτ_entry h 0 0).add (continuousAt_Nτ_entry h 1 1)
end FriedCrossing.Derived
