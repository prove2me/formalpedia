-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_contDiff_E_f_b048a987d2d2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:05:48.976074+00:00
-- url     : https://prove2.me/submissions/f75b0221-dd22-4fff-b649-f175ac80b6bc

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_contDiff_E__fcc4cec339ab

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A) : ContDiff ℝ 3 fun q : ℝ × ℝ => E₁f M A q.1 q.2 :=
  contDiff_E₁ (A := fun q : ℝ × ℝ => A q.1 q.2) (M := fun q : ℝ × ℝ => M q.1 q.2) h.deg2 h.deg1
end FriedCrossing.Derived
