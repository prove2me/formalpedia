-- Prove2me | solution 1 for P2M_FriedCrossing_Spectral_E__mirror_bf3c94cb1a0c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:03:40.43748+00:00
-- url     : https://prove2.me/submissions/2fd4176d-d7a7-4a62-9c88-8389e8c2252a

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_ClusterMatrix_trace_smul_one
import Theorems.Thm_FriedCrossing_ClusterMatrix_det_smul_one
import Theorems.Thm_FriedCrossing_Spectral_coeffs_of_mirror

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ} {s : ℝ}
    (hM : M = s • (1 : Matrix (Fin 2) (Fin 2) ℝ))
    (hA : ∀ z, A.charpoly.eval z = (z - s) ^ 3 * (z + s)) : E₂ A M = -s ^ 2 := by
  obtain ⟨h1, h2⟩ := coeffs_of_mirror hA
  rw [E₂, E₁, h1, h2, hM, trace_smul_one, det_smul_one]; ring
end FriedCrossing.Spectral
