-- Prove2me | solution 1 for ProjectiveMeasurementEquilibration.lindblad_tendsto_pinching
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-02T19:32:06.628159+00:00
-- url     : https://prove2.me/submissions/a7c72837-4a86-4471-a511-3337fd116b0b

import Definitions.Def_pme_quantum_basics
import Theorems.Thm_ProjectiveMeasurementEquilibration_block_decomposition
import Theorems.Thm_ProjectiveMeasurementEquilibration_lindblad_block_solution
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Instances.Matrix
import Mathlib.Tactic.Ring

open Matrix Filter Topology ProjectiveMeasurementEquilibration

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

theorem solution {n : Type} [Fintype n] [DecidableEq n] {X : Matrix n n ℂ}
    (hX : X.IsHermitian) (ρ : Matrix n n ℂ) (_hρ : IsDensityMatrix ρ) :
    (∃ ρt : ℝ → Matrix n n ℂ, IsLindbladSolution X ρ ρt) ∧
    ∀ ρt : ℝ → Matrix n n ℂ, IsLindbladSolution X ρ ρt →
      Tendsto ρt atTop (𝓝 (pinching hX ρ)) := by
  classical
  let G := Unitary.conjStarAlgAut ℂ (Matrix n n ℂ) hX.eigenvectorUnitary
  let F := G.symm
  have hFG (A : Matrix n n ℂ) : F (G A) = A := G.symm_apply_apply A
  let a : n → n → ℝ := fun i j => (hX.eigenvalues i - hX.eigenvalues j) ^ 2 / 2
  let B : ℝ → Matrix n n ℂ := fun t i j => (Real.exp (-a i j * t) : ℂ) * F ρ i j
  let B' : ℝ → Matrix n n ℂ := fun t i j => -(a i j : ℂ) * B t i j
  have hFX : F X = diagonal (fun i => (hX.eigenvalues i : ℂ)) := by
    simpa [F, G, Function.comp_def] using hX.conjStarAlgAut_star_eigenvectorUnitary
  have hgen (A : Matrix n n ℂ) (i j : n) :
      F (lindbladian X A) i j = -(a i j : ℂ) * F A i j := by
    simp only [lindbladian, map_sub, map_mul, map_add, map_smul, hFX,
      diagonal_mul_diagonal, diagonal_mul, mul_diagonal, Matrix.sub_apply,
      Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    dsimp [a]
    push_cast
    ring
  have hB (t : ℝ) : HasDerivWithinAt B (B' t) (Set.Ici 0) t := by
    apply hasDerivWithinAt_pi.mpr
    intro i
    apply hasDerivWithinAt_pi.mpr
    intro j
    have he := (Complex.ofRealCLM.hasFDerivAt).comp_hasDerivAt t
      (((hasDerivAt_id t).const_mul (-a i j)).exp)
    have he' : HasDerivAt (fun u : ℝ => (Real.exp (-a i j * u) : ℂ))
        ((Real.exp (-a i j * t) : ℂ) * (-a i j : ℂ)) t := by
      simpa [Function.comp_def] using he
    convert he'.hasDerivWithinAt.mul_const (F ρ i j) using 1 <;> first | rfl | (dsimp [B']; ring)
  constructor
  · refine ⟨fun t => G (B t), ?_, ?_⟩
    · change G (B 0) = ρ
      have hB0 : B 0 = F ρ := by ext i j; simp [B]
      rw [hB0]
      exact G.apply_symm_apply ρ
    · intro t ht
      have hmat : G (B' t) = lindbladian X (G (B t)) := by
        apply F.injective
        change F (G (B' t)) = F (lindbladian X (G (B t)))
        rw [hFG]
        ext i j
        rw [hgen, hFG]
      rw [← hmat]
      apply hasDerivWithinAt_pi.mpr
      intro i
      apply hasDerivWithinAt_pi.mpr
      intro j
      exact mul_entry_deriv (hX.eigenvectorUnitary : Matrix n n ℂ)
        (star (hX.eigenvectorUnitary : Matrix n n ℂ)) B (B' t)
        (hB t) i j
  · intro ρt hsol
    have hrep : ∀ᶠ t : ℝ in atTop, ρt t =
        ∑ x ∈ eigenvalueSet hX, ∑ y ∈ eigenvalueSet hX,
          (Real.exp (-(t / 2) * (x - y) ^ 2) : ℂ) •
            (eigenproj hX x * ρ * eigenproj hX y) := by
      filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
      rw [← block_decomposition hX (ρt t)]
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      exact lindblad_block_solution hX ρ ρt hsol t ht x y
    have hterm (x y : ℝ) :
        Tendsto (fun t : ℝ => (Real.exp (-(t / 2) * (x - y) ^ 2) : ℂ) •
          (eigenproj hX x * ρ * eigenproj hX y)) atTop
          (𝓝 (if x = y then eigenproj hX x * ρ * eigenproj hX y else 0)) := by
      by_cases hxy : x = y
      · subst y
        simp
      · have ha : 0 < (x - y) ^ 2 / 2 := div_pos (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy)) (by norm_num)
        have he : Tendsto (fun t : ℝ => Real.exp (-(t / 2) * (x - y) ^ 2)) atTop (𝓝 0) := by
          have hh := Real.tendsto_exp_neg_atTop_nhds_zero.comp
            (tendsto_id.const_mul_atTop ha)
          convert hh using 1
          ext t
          simp only [Function.comp_apply, id_eq]
          congr 1
          ring
        have hc : Tendsto (fun t : ℝ => (Real.exp (-(t / 2) * (x - y) ^ 2) : ℂ))
            atTop (𝓝 (0 : ℂ)) := by
          simpa only [Function.comp_def, Complex.ofReal_zero] using
            Complex.continuous_ofReal.continuousAt.tendsto.comp he
        simpa only [hxy, if_false, zero_smul] using hc.smul
          (tendsto_const_nhds (x := eigenproj hX x * ρ * eigenproj hX y))
    have hsum := tendsto_finsetSum (eigenvalueSet hX) fun x hx =>
      tendsto_finsetSum (eigenvalueSet hX) fun y hy => hterm x y
    have hend : (∑ x ∈ eigenvalueSet hX, ∑ y ∈ eigenvalueSet hX,
        if x = y then eigenproj hX x * ρ * eigenproj hX y else 0) = pinching hX ρ := by
      simp [pinching]
    rw [hend] at hsum
    apply hsum.congr'
    filter_upwards [hrep] with t ht
    exact ht.symm
