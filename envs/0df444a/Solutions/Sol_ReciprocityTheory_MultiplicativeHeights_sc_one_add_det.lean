-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.sc_one_add_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:31:06.389693+00:00
-- url     : https://prove2.me/submissions/ba0c3dba-146d-4764-855d-0997ccecb69a

import Mathlib
import Definitions.Def_ReciprocityTheory_SemistableReduction_SemiContractA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.MultiplicativeHeights
open Matrix
open scoped ComplexOrder
private theorem one_lt_re_det_one_add_and_im_eq_zero_of_posDef {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {Q : Matrix m m ℂ} (hQ : Q.PosDef) : 1 < ((1 + Q).det).re ∧ ((1 + Q).det).im = 0 := by
  have hsp := hQ.isHermitian.spectral_theorem
  rw [Unitary.conjStarAlgAut_apply] at hsp
  obtain ⟨U, hU⟩ : ∃ U : Matrix m m ℂ, U = (hQ.isHermitian.eigenvectorUnitary : Matrix m m ℂ) :=
    ⟨_, rfl⟩
  have hUU : U * star U = 1 := by
    rw [hU]
    exact Matrix.mem_unitaryGroup_iff.mp hQ.isHermitian.eigenvectorUnitary.2
  obtain ⟨d, hd⟩ : ∃ d : m → ℝ, d = hQ.isHermitian.eigenvalues := ⟨_, rfl⟩
  have hdpos : ∀ i, 0 < d i := fun i => by rw [hd]; exact hQ.eigenvalues_pos i
  rw [← hU, ← hd] at hsp

  have h1 : 1 + Q = U * (1 + diagonal (RCLike.ofReal ∘ d)) * star U := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hUU, ← hsp]
  have hdet : (1 + Q).det = ((∏ i, (1 + d i) : ℝ) : ℂ) := by
    rw [h1, det_mul, det_mul, mul_comm U.det, mul_assoc, ← det_mul, hUU, det_one, mul_one,
      ← diagonal_one, diagonal_add, det_diagonal]
    push_cast
    rfl
  rw [hdet, Complex.ofReal_re, Complex.ofReal_im]
  refine ⟨?_, rfl⟩
  calc (1 : ℝ) = ∏ _i : m, (1 : ℝ) := by simp
    _ < ∏ i, (1 + d i) := Finset.prod_lt_prod_of_nonempty (fun _ _ => one_pos)
        (fun i _ => by linarith [hdpos i]) Finset.univ_nonempty
end ReciprocityTheory.MultiplicativeHeights
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open Matrix
open scoped ComplexOrder
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {m : Type*} [Fintype m] [DecidableEq m] [Nonempty m]
    {Q : Matrix m m ℂ} (hQ : Q.PosDef) : 1 < ((1 + Q).det).re := by
  exact (one_lt_re_det_one_add_and_im_eq_zero_of_posDef hQ).1
end ReciprocityTheory.MultiplicativeHeights
