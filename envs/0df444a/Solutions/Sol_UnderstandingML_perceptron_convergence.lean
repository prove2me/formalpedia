-- Prove2me | solution 1 for UnderstandingML.perceptron_convergence
-- status  : ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-25T14:46:22.689446+00:00
-- url     : https://prove2.me/submissions/819592a0-0fab-4f72-bb5a-9149e3b22a6f

import Definitions.Def_UnderstandingML_Linear

open MeasureTheory
open scoped InnerProductSpace

namespace UnderstandingML.PerceptronProof

variable {d m : ℕ}

/-- Every example norm is bounded by `R = maxᵢ ‖xᵢ‖`. -/
lemma norm_le_radius (x : Fin m → Vec d) (i : Fin m) : ‖x i‖ ≤ radius x :=
  le_ciSup (f := fun j => ‖x j‖) (Set.finite_range _).bddAbove i

lemma radius_nonneg (x : Fin m → Vec d) : 0 ≤ radius x := by
  rcases isEmpty_or_nonempty (Fin m) with h | ⟨⟨i⟩⟩
  · simp [radius, Real.iSup_of_isEmpty]
  · exact (norm_nonneg _).trans (norm_le_radius x i)

/-- First invariant: `⟨w*, w⁽ᵗ⁾⟩ ≥ t` along a run. -/
lemma inner_ge (x : Fin m → Vec d) (y : Fin m → ℝ) (w : ℕ → Vec d) (T : ℕ)
    (hrun : IsPerceptronRun x y w T) (ws : Vec d) (hws : ∀ i, 1 ≤ y i * ⟪ws, x i⟫_ℝ) :
    ∀ t ≤ T, (t : ℝ) ≤ ⟪ws, w t⟫_ℝ := by
  intro t
  induction t with
  | zero => intro _; simp [hrun.1]
  | succ t ih =>
    intro ht
    obtain ⟨i, -, hi⟩ := hrun.2 t (by omega)
    have := ih (by omega)
    rw [hi, inner_add_right, inner_smul_right]
    push_cast
    linarith [hws i]

/-- Second invariant: `‖w⁽ᵗ⁾‖² ≤ t R²` along a run. -/
lemma norm_sq_le (x : Fin m → Vec d) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (w : ℕ → Vec d) (T : ℕ) (hrun : IsPerceptronRun x y w T) :
    ∀ t ≤ T, ‖w t‖ ^ 2 ≤ t * radius x ^ 2 := by
  intro t
  induction t with
  | zero => intro _; simp [hrun.1]
  | succ t ih =>
    intro ht
    obtain ⟨i, hmis, hi⟩ := hrun.2 t (by omega)
    have := ih (by omega)
    have hy2 : y i ^ 2 = 1 := by rcases hy i with h | h <;> simp [h]
    have hR : ‖x i‖ ^ 2 ≤ radius x ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_le_radius x i) 2
    rw [hi, norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
      hy2]
    push_cast
    nlinarith

/-- Bound for a single feasible vector `w*`: `T ≤ (R‖w*‖)²`. -/
lemma run_le_of_feasible (x : Fin m → Vec d) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (w : ℕ → Vec d) (T : ℕ) (hrun : IsPerceptronRun x y w T) (ws : Vec d)
    (hws : ∀ i, 1 ≤ y i * ⟪ws, x i⟫_ℝ) :
    (T : ℝ) ≤ (radius x * ‖ws‖) ^ 2 := by
  have h1 := inner_ge x y w T hrun ws hws T le_rfl
  have h2 := norm_sq_le x y hy w T hrun T le_rfl
  have hcs : ⟪ws, w T⟫_ℝ ≤ ‖ws‖ * ‖w T‖ := real_inner_le_norm _ _
  have hT : (0 : ℝ) ≤ T := Nat.cast_nonneg T
  -- `T² ≤ ‖w*‖² ‖w T‖² ≤ ‖w*‖² T R²`
  have hsq : (T : ℝ) ^ 2 ≤ ‖ws‖ ^ 2 * (T * radius x ^ 2) := by
    have : (T : ℝ) ^ 2 ≤ (‖ws‖ * ‖w T‖) ^ 2 :=
      pow_le_pow_left₀ hT (h1.trans hcs) 2
    rw [mul_pow] at this
    exact this.trans (mul_le_mul_of_nonneg_left h2 (sq_nonneg _))
  rcases hT.lt_or_eq with hpos | hzero
  · have : (T : ℝ) * T ≤ T * (radius x * ‖ws‖) ^ 2 := by nlinarith
    exact le_of_mul_le_mul_left this hpos
  · rw [← hzero]; positivity

/-- Separability gives a vector with margin one (Equation (9.1)). -/
lemma exists_feasible (x : Fin m → Vec d) (y : Fin m → ℝ) (hsep : Separable x y) :
    ∃ ws : Vec d, ∀ i, 1 ≤ y i * ⟪ws, x i⟫_ℝ := by
  obtain ⟨w, hw⟩ := hsep
  rcases isEmpty_or_nonempty (Fin m) with h | h
  · exact ⟨0, fun i => isEmptyElim i⟩
  · obtain ⟨j, -, hj⟩ := Finset.exists_min_image Finset.univ (fun i => y i * ⟪w, x i⟫_ℝ)
      Finset.univ_nonempty
    have hγ := hw j
    refine ⟨(y j * ⟪w, x j⟫_ℝ)⁻¹ • w, fun i => ?_⟩
    rw [inner_smul_left, RCLike.conj_to_real, mul_left_comm, ← div_eq_inv_mul, one_le_div hγ]
    exact hj i (Finset.mem_univ i)

/-- Part 1 of Theorem 9.1: every run has at most `(RB)²` iterations. -/
lemma run_le (x : Fin m → Vec d) (y : Fin m → ℝ) (hy : ∀ i, y i = 1 ∨ y i = -1)
    (hsep : Separable x y) (w : ℕ → Vec d) (T : ℕ) (hrun : IsPerceptronRun x y w T) :
    (T : ℝ) ≤ (radius x * marginNorm x y) ^ 2 := by
  obtain ⟨ws0, hws0⟩ := exists_feasible x y hsep
  have hR := radius_nonneg x
  have hne : {r | ∃ w : Vec d, ‖w‖ = r ∧ ∀ i, 1 ≤ y i * ⟪w, x i⟫_ℝ}.Nonempty :=
    ⟨_, ws0, rfl, hws0⟩
  have hB0 : 0 ≤ marginNorm x y := by
    apply le_csInf hne
    rintro r ⟨w, rfl, -⟩
    exact norm_nonneg _
  rcases hR.lt_or_eq with hRpos | hR0
  · -- `√T / R ≤ ‖w*‖` for every feasible `w*`, hence `√T / R ≤ B`.
    have key : Real.sqrt T / radius x ≤ marginNorm x y := by
      apply le_csInf hne
      rintro r ⟨ws, rfl, hws⟩
      have h := run_le_of_feasible x y hy w T hrun ws hws
      rw [div_le_iff₀ hRpos, Real.sqrt_le_left (by positivity)]
      nlinarith
    have hs : Real.sqrt T ≤ radius x * marginNorm x y := by
      rw [div_le_iff₀ hRpos] at key; linarith
    have := pow_le_pow_left₀ (Real.sqrt_nonneg _) hs 2
    rwa [Real.sq_sqrt (Nat.cast_nonneg _)] at this
  · have h := run_le_of_feasible x y hy w T hrun ws0 hws0
    rw [← hR0] at h ⊢
    simpa using h

open Classical in
/-- One greedy step of the Batch Perceptron: update on some mistaken example if there is one. -/
noncomputable def step (x : Fin m → Vec d) (y : Fin m → ℝ) (v : Vec d) : Vec d :=
  if h : ∃ i, y i * ⟪v, x i⟫_ℝ ≤ 0 then v + y h.choose • x h.choose else v

/-- The greedy run. -/
noncomputable def greedy (x : Fin m → Vec d) (y : Fin m → ℝ) (t : ℕ) : Vec d :=
  (step x y)^[t] 0

lemma greedy_succ (x : Fin m → Vec d) (y : Fin m → ℝ) (t : ℕ) :
    greedy x y (t + 1) = step x y (greedy x y t) := by
  simp [greedy, Function.iterate_succ_apply']

lemma greedy_run (x : Fin m → Vec d) (y : Fin m → ℝ) (T : ℕ)
    (hT : ∀ t < T, ∃ i, y i * ⟪greedy x y t, x i⟫_ℝ ≤ 0) :
    IsPerceptronRun x y (greedy x y) T := by
  refine ⟨rfl, fun t ht => ?_⟩
  have h := hT t ht
  refine ⟨h.choose, h.choose_spec, ?_⟩
  rw [greedy_succ, step, dif_pos h]

end UnderstandingML.PerceptronProof

open UnderstandingML UnderstandingML.PerceptronProof in
theorem solution {d m : ℕ} (x : Fin m → Vec d) (y : Fin m → ℝ)
    (hy : ∀ i, y i = 1 ∨ y i = -1) (hsep : Separable x y) :
    (∀ (w : ℕ → Vec d) (T : ℕ), IsPerceptronRun x y w T →
        (T : ℝ) ≤ (radius x * marginNorm x y) ^ 2) ∧
    ∃ (w : ℕ → Vec d) (T : ℕ), IsPerceptronRun x y w T ∧
      (T : ℝ) ≤ (radius x * marginNorm x y) ^ 2 ∧ ∀ i, 0 < y i * ⟪w T, x i⟫_ℝ := by
  classical
  refine ⟨fun w T hrun => run_le x y hy hsep w T hrun, ?_⟩
  have hex : ∃ t, ∀ i, 0 < y i * ⟪greedy x y t, x i⟫_ℝ := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨N, hN⟩ := exists_nat_gt ((radius x * marginNorm x y) ^ 2)
    have := run_le x y hy hsep (greedy x y) N (greedy_run x y N fun t _ => hcon t)
    linarith
  have hrun : IsPerceptronRun x y (greedy x y) (Nat.find hex) :=
    greedy_run x y _ fun t ht => by
      have := Nat.find_min hex ht
      push_neg at this
      exact this
  exact ⟨greedy x y, Nat.find hex, hrun, run_le x y hy hsep _ _ hrun, Nat.find_spec hex⟩
