-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HermitianFormComparison_sum_norm_sq_unitary_a75e483de46a
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:30:15.67618+00:00
-- url     : https://prove2.me/submissions/8167dd81-d243-4673-a6fa-9e19717b8609

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsHermFormCompare
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PHermFormCompare

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
theorem _root_.solution {n : ℕ} (U : Matrix (Fin n) (Fin n) ℂ) (hU : U * star U = 1)
    (x : Fin n → ℂ) : ∑ k, ‖(star U *ᵥ x) k‖ ^ 2 = (star x ⬝ᵥ x).re := by
  have h1 : star (star U *ᵥ x) ⬝ᵥ (star U *ᵥ x) = star x ⬝ᵥ x := by
    rw [star_mulVec, dotProduct_mulVec, vecMul_vecMul, star_eq_conjTranspose,
      conjTranspose_conjTranspose, ← star_eq_conjTranspose, hU, vecMul_one]
  rw [← h1]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
end GroundTheory.Heights₂.Heights.HermitianFormComparison
