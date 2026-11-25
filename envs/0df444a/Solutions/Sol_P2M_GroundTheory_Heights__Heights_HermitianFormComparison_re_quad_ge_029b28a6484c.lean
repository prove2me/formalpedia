-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_ge_029b28a6484c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:29:50.041743+00:00
-- url     : https://prove2.me/submissions/ff65c7c5-dc51-47c7-bf73-1680672710e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_sum_norm_sq_unitary_a75e483de46a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_eq_3680ef59eee8
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HermitianFormComparison_eigenvectorUnitary_mul_star_38f790feae40

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open Matrix
open scoped ComplexOrder
open GroundTheory.Heights₂.Heights.HermitianFormComparison
namespace GroundTheory.Heights₂.Heights.HermitianFormComparison
theorem _root_.solution {n : ℕ} {N : Matrix (Fin n) (Fin n) ℂ} (hN : N.PosDef) (x : Fin n → ℂ) :
    (1 + ∑ k, (hN.1.eigenvalues k)⁻¹)⁻¹ * (star x ⬝ᵥ x).re ≤ (star x ⬝ᵥ (N *ᵥ x)).re := by
  rw [re_quad_eq hN.1, ← sum_norm_sq_unitary _ (eigenvectorUnitary_mul_star hN.1), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hpos := hN.eigenvalues_pos k
  have hle : (hN.1.eigenvalues k)⁻¹ ≤ ∑ j, (hN.1.eigenvalues j)⁻¹ :=
    Finset.single_le_sum (f := fun j => (hN.1.eigenvalues j)⁻¹)
      (fun j _ => (inv_pos.mpr (hN.eigenvalues_pos j)).le) (Finset.mem_univ k)
  rw [inv_le_comm₀ (by linarith [inv_pos.mpr hpos]) hpos]
  linarith
end GroundTheory.Heights₂.Heights.HermitianFormComparison
