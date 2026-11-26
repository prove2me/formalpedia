-- Prove2me | solution 1 for P2M_FriedCrossing_Spectral_E__pinned_89a5c3e78b6a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:04:01.544805+00:00
-- url     : https://prove2.me/submissions/554f344b-1afb-4082-bfeb-64a01639d2ce

import Definitions.Def_B1s_fried_crossing_purezeros_9_08
import Definitions.Def_B1s_fried_cluster_matrices_9_10
import Theorems.Thm_FriedCrossing_Spectral_coeffs_of_pinned

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix Polynomial
open FriedCrossing.Spectral
open ClusterMatrix
namespace FriedCrossing.Spectral
theorem _root_.solution {A : Matrix (Fin 4) (Fin 4) ℝ} {M : Matrix (Fin 2) (Fin 2) ℝ}
    (hA : ∀ z, A.charpoly.eval z = z ^ 3 * (z - M.trace)) : E₁ A M = 0 := by
  obtain ⟨h1, _⟩ := coeffs_of_pinned hA
  rw [E₁, h1]; ring
end FriedCrossing.Spectral
