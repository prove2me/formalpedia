-- Prove2me | solution 1 for ReciprocityTheory.GeometryOfNumbersTheory.gramSt_det_one_add_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:01:35.401581+00:00
-- url     : https://prove2.me/submissions/ba1fdb77-3808-42e9-96c6-8197c16828a3

import Mathlib
import Definitions.Def_ReciprocityTheory_GeometryOfNumbers_LatticeCovolumes_GramSt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.GeometryOfNumbersTheory
open Matrix
open scoped ComplexOrder MatrixOrder
variable {ι : Type*} [Fintype ι] [DecidableEq ι]
namespace ReciprocityTheory.GeometryOfNumbersTheory
theorem _root_.solution {Q : Matrix ι ι ℂ} (hQ : Q.PosSemidef) :
    (1 + Q).det = ((∏ i, (1 + hQ.1.eigenvalues i) : ℝ) : ℂ) := by
  set U := hQ.1.eigenvectorUnitary
  have hspec := hQ.1.spectral_theorem
  have h1 : (1 + Q) = Unitary.conjStarAlgAut ℂ _ U
      (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues)) := by
    rw [map_add, map_one, ← hspec]
  have hd : (1 + diagonal (RCLike.ofReal ∘ hQ.1.eigenvalues) : Matrix ι ι ℂ) =
      diagonal (fun i => ((1 + hQ.1.eigenvalues i : ℝ) : ℂ)) := by
    ext i j
    by_cases h : i = j
    · subst h; simp
    · simp [h, one_apply]
  rw [h1, Unitary.conjStarAlgAut_apply, hd, det_mul, det_mul, det_diagonal, Complex.ofReal_prod]
  rw [mul_comm (det _) (∏ _, _), mul_assoc, ← det_mul]
  try rw [Unitary.coe_star]
  rw [Unitary.mul_star_self_of_mem U.2, det_one, mul_one]
end ReciprocityTheory.GeometryOfNumbersTheory
