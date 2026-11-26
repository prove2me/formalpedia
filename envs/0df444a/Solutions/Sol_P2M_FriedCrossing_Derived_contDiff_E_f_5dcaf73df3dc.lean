-- Prove2me | solution 1 for P2M_FriedCrossing_Derived_contDiff_E_f_5dcaf73df3dc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:07:12.728955+00:00
-- url     : https://prove2.me/submissions/4d0f1497-8b0b-463b-b9c2-035843fc8b47

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_P2M_FriedCrossing_ClusterMatrix_contDiff_E__fe65e108e397

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Derived
open Regularity HQuot Hadamard ClusterMatrix Ledger
variable {M : ℝ → ℝ → Matrix (Fin 2) (Fin 2) ℝ} {A : ℝ → ℝ → Matrix (Fin 4) (Fin 4) ℝ}
  {sStar : ℝ → ℝ}
namespace FriedCrossing.Derived
theorem _root_.solution (h : ClusterC3 M A) : ContDiff ℝ 3 fun q : ℝ × ℝ => E₂f M A q.1 q.2 :=
  contDiff_E₂ (A := fun q : ℝ × ℝ => A q.1 q.2) (M := fun q : ℝ × ℝ => M q.1 q.2) h.deg2 h.deg1
end FriedCrossing.Derived
