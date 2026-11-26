-- Prove2me | solution 1 for P2M_FriedCrossing_Spectral_E__pinned_8575cb4e933f
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:04:02.008016+00:00
-- url     : https://prove2.me/submissions/17b5b5c3-2c71-40b7-b1f5-1372f99d64aa

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
    (hdet : M.det = 0) (hA : ∀ z, A.charpoly.eval z = z ^ 3 * (z - M.trace)) : E₂ A M = 0 := by
  obtain ⟨h1, h2⟩ := coeffs_of_pinned hA
  rw [E₂, E₁, h1, h2, hdet]; ring
end FriedCrossing.Spectral
