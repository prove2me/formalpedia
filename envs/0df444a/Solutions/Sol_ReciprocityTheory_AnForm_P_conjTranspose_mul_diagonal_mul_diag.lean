-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.conjTranspose_mul_diagonal_mul_diag
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:07:05.834601+00:00
-- url     : https://prove2.me/submissions/d065a2b4-867f-46d8-9ebb-faf5fd3346ea

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (hd : Fin N → ℝ) (m : ℕ) (hm : m ≤ N) (v : Pairs N → ℂ) (a : Fin m) :
    ((Zm N m hm v)ᴴ * (diagonal fun a => (hd (Fin.castLE hm a) : ℂ)) * Zm N m hm v) a a =
      ∑ b : Fin m, star (zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) *
        ((hd (Fin.castLE hm b) : ℂ) * zMat N v (Fin.castLE hm b) (Fin.castLE hm a)) := by
  rw [Matrix.mul_apply]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [Matrix.mul_diagonal, conjTranspose_apply, Zm, submatrix_apply]
  ring
end ReciprocityTheory.AnForm.P
