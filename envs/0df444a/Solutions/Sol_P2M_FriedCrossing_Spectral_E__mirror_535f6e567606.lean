-- Prove2me | solution 1 for P2M_FriedCrossing_Spectral_E__mirror_535f6e567606
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:03:11.664369+00:00
-- url     : https://prove2.me/submissions/fceefad6-5dfd-4038-823d-2f4d7b8a8f5b

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_ClusterMatrix_trace_smul_one
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
    (hA : ∀ z, A.charpoly.eval z = (z - s) ^ 3 * (z + s)) : E₁ A M = 0 := by
  obtain ⟨h1, _⟩ := coeffs_of_mirror hA
  rw [E₁, h1, hM, trace_smul_one]; ring
end FriedCrossing.Spectral
