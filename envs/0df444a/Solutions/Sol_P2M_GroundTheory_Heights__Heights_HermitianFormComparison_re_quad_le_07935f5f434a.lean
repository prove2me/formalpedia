-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianFormComparison_re_quad_le_07935f5f434a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:30:16.952069+00:00
-- url     : https://prove2.me/submissions/0702b2a8-9026-4212-a795-7949a1af2fce

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
theorem _root_.solution {n : ℕ} {M : Matrix (Fin n) (Fin n) ℂ} (hM : M.PosSemidef) (x : Fin n → ℂ) :
    (star x ⬝ᵥ (M *ᵥ x)).re ≤ (1 + ∑ k, hM.1.eigenvalues k) * (star x ⬝ᵥ x).re := by
  rw [re_quad_eq hM.1, ← sum_norm_sq_unitary _ (eigenvectorUnitary_mul_star hM.1), Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hle : hM.1.eigenvalues k ≤ ∑ j, hM.1.eigenvalues j :=
    Finset.single_le_sum (f := hM.1.eigenvalues) (fun j _ => hM.eigenvalues_nonneg j) (Finset.mem_univ k)
  linarith
end GroundTheory.Heights₂.Heights.HermitianFormComparison
