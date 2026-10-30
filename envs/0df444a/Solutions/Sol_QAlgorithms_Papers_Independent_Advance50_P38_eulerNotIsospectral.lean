-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Advance50.P38.eulerNotIsospectral
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T09:18:19.460993+00:00
-- url     : https://prove2.me/submissions/cd74aeed-6530-4dff-bcd1-baba06863656

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Advance50_P38

namespace QAlgorithms.Papers.Independent.Advance50.P38

open scoped BigOperators Topology Manifold ContDiff

noncomputable section

lemma euler_explicit (a : ℝ) :
    orbitEulerStep (!![(1:ℂ), 0; 0, -1]) (!![(0:ℂ), 1; 1, 0]) a = !![(1:ℂ), 4 * (a:ℂ); 4 * (a:ℂ), -1] := by
  have hC : (!![(0:ℂ), 1; 1, 0]).conjTranspose = !![(0:ℂ), 1; 1, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  have h1 : comm (!![(1:ℂ), 0; 0, -1]) (!![(0:ℂ), 1; 1, 0]) = !![(0:ℂ), 2; -2, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [comm, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  have hM : (!![(0:ℂ), 2; -2, 0]).conjTranspose = !![(0:ℂ), -2; 2, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  have h2 : skew (!![(0:ℂ), 2; -2, 0]) = !![(0:ℂ), 2; -2, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [skew, hM] <;> norm_num
  have h3 : comm (!![(1:ℂ), 0; 0, -1]) (!![(0:ℂ), 2; -2, 0]) = !![(0:ℂ), 4; 4, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [comm, Matrix.mul_apply, Fin.sum_univ_two] <;> norm_num
  unfold orbitEulerStep
  rw [hC, h1, h2, h3]
  ext i j; fin_cases i <;> fin_cases j <;> simp <;> ring

end

end QAlgorithms.Papers.Independent.Advance50.P38

open QAlgorithms.Papers.Independent.Advance50.P38 in
theorem solution :
    ∃ X C : (Matrix (Fin 2) (Fin 2) ℂ), X.IsHermitian ∧ C.IsHermitian ∧
      ∀ a : ℝ, 0 < a → (orbitEulerStep X C a).charpoly ≠ X.charpoly := by
  refine ⟨!![(1:ℂ), 0; 0, -1], !![(0:ℂ), 1; 1, 0], ?_, ?_, ?_⟩
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.conjTranspose_apply]
  · intro a ha h
    rw [euler_explicit] at h
    have h0 := congrArg (fun p => Polynomial.eval 0 p) h
    simp [Matrix.charpoly_fin_two] at h0
    exact ha.ne' (by first | exact h0.symm | exact h0)
