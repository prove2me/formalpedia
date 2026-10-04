-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.lindblad_block_solution
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T19:26:58.180075+00:00
-- url     : https://prove2.me/submissions/344567c4-5dfe-4c9e-b14b-c043f108d6ff

import Definitions.Def_pme_quantum_basics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Ring

open Matrix ProjectiveMeasurementEquilibration

private theorem mul_entry_deriv {n : Type} [Fintype n] [DecidableEq n]
    (P Q : Matrix n n ℂ) (f : ℝ → Matrix n n ℂ) (f' : Matrix n n ℂ)
    {s : Set ℝ} {t : ℝ} (hf : HasDerivWithinAt f f' s t) (i j : n) :
    HasDerivWithinAt (fun u => (P * f u * Q) i j) ((P * f' * Q) i j) s t := by
  classical
  simp only [Matrix.mul_apply]
  apply HasDerivWithinAt.fun_sum
  intro k hk
  apply HasDerivWithinAt.mul_const
  apply HasDerivWithinAt.fun_sum
  intro l hl
  exact ((hasDerivWithinAt_pi.mp (hasDerivWithinAt_pi.mp hf l)) k).const_mul (P i l)

private theorem scalar_decay (a : ℝ) (f : ℝ → ℂ)
    (hf : ∀ t, 0 ≤ t → HasDerivWithinAt f (-(a : ℂ) * f t) (Set.Ici 0) t)
    (t : ℝ) (ht : 0 ≤ t) : f t = (Real.exp (-a * t) : ℂ) * f 0 := by
  let g := fun u : ℝ => (Real.exp (a * u) : ℂ) * f u
  have hg (u : ℝ) (hu : u ∈ Set.Ici 0) : HasDerivWithinAt g 0 (Set.Ici 0) u := by
    have he := (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt u
      (((hasDerivAt_id u).const_mul a).exp)
    have he' : HasDerivWithinAt (fun v : ℝ => (Real.exp (a * v) : ℂ))
        ((Real.exp (a * u) : ℂ) * (a : ℂ)) (Set.Ici 0) u := by
      simpa [Function.comp_def] using he.hasDerivWithinAt
    convert he'.mul (hf u hu) using 1 <;> first | rfl | ring
  have heq : g t = g 0 := (convex_Ici (0 : ℝ)).is_const_of_fderivWithin_eq_zero
    (fun u hu => (hg u hu).differentiableWithinAt)
    (fun u hu => by
      simpa using ((hg u hu).hasFDerivWithinAt.fderivWithin
        (uniqueDiffOn_Ici 0 u hu))) ht (Set.self_mem_Ici)
  have hcancel : (Real.exp (-a * t) : ℂ) * (Real.exp (a * t) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  have heq' : (Real.exp (a * t) : ℂ) * f t = f 0 := by
    simpa only [g, mul_zero, Real.exp_zero, Complex.ofReal_one, one_mul] using heq
  calc
    f t = 1 * f t := (one_mul _).symm
    _ = ((Real.exp (-a * t) : ℂ) * (Real.exp (a * t) : ℂ)) * f t := by rw [hcancel]
    _ = (Real.exp (-a * t) : ℂ) * f 0 := by rw [mul_assoc, heq']

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (ρ : Matrix n n ℂ) (ρt : ℝ → Matrix n n ℂ)
    (hsol : IsLindbladSolution X ρ ρt) (t : ℝ) (ht : 0 ≤ t) (x y : ℝ) :
    eigenproj hX x * ρt t * eigenproj hX y =
      ((Real.exp (-(t / 2) * (x - y) ^ 2) : ℝ) : ℂ) •
        (eigenproj hX x * ρ * eigenproj hX y) := by
  classical
  let G := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hX.eigenvectorUnitary
  let F := G.symm
  let D : ℝ → Matrix n n ℂ := fun z =>
    diagonal (fun i => if hX.eigenvalues i = z then (1 : ℂ) else 0)
  have heig (z : ℝ) : F (eigenproj hX z) = D z := by
    change G.symm (G (D z)) = D z
    exact G.symm_apply_apply (D z)
  have hFX : F X = diagonal (fun i => (hX.eigenvalues i : ℂ)) := by
    simpa [F, G, Function.comp_def] using hX.conjStarAlgAut_star_eigenvectorUnitary
  have hL (A : Matrix n n ℂ) :
      eigenproj hX x * lindbladian X A * eigenproj hX y =
        (-(((x - y) ^ 2 / 2 : ℝ) : ℂ)) • (eigenproj hX x * A * eigenproj hX y) := by
    apply F.injective
    change F _ = F _
    simp only [lindbladian, map_mul, map_sub, map_add, map_smul, heig, hFX]
    ext i j
    simp only [D, diagonal_mul, mul_diagonal, diagonal_mul_diagonal, Matrix.sub_apply, Matrix.add_apply,
      Matrix.smul_apply, smul_eq_mul]
    by_cases hi : hX.eigenvalues i = x <;> by_cases hj : hX.eigenvalues j = y
    · simp only [hi, hj, if_true, one_mul, mul_one]
      push_cast
      ring
    all_goals simp [hi, hj]
  ext i j
  have hf (u : ℝ) (hu : 0 ≤ u) := mul_entry_deriv (eigenproj hX x) (eigenproj hX y)
    ρt (lindbladian X (ρt u)) (hsol.2 u hu) i j
  have hf' (u : ℝ) (hu : 0 ≤ u) :
      HasDerivWithinAt (fun v => (eigenproj hX x * ρt v * eigenproj hX y) i j)
        (-(((x - y) ^ 2 / 2 : ℝ) : ℂ) *
          (eigenproj hX x * ρt u * eigenproj hX y) i j) (Set.Ici 0) u := by
    simpa only [hL, Matrix.smul_apply, smul_eq_mul] using hf u hu
  have h := scalar_decay ((x - y) ^ 2 / 2)
    (fun v => (eigenproj hX x * ρt v * eigenproj hX y) i j) hf' t ht
  have hexp : -((x - y) ^ 2 / 2) * t = -(t / 2) * (x - y) ^ 2 := by ring
  simpa only [hsol.1, hexp, Matrix.smul_apply, smul_eq_mul] using h
