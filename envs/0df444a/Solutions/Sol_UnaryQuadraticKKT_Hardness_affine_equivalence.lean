-- Prove2me | solution 1 for UnaryQuadraticKKT.Hardness.affine_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @CGTMoyano
-- created : 2026-11-24T15:57:59.960847+00:00
-- url     : https://prove2.me/submissions/da82f4c1-2a6d-4a52-932b-faa31ef3179f

import Mathlib
import Definitions.Def_UnaryQuadraticKKT_Hardness_Combined

set_option autoImplicit false

open UnaryQuadraticKKT.Hardness NetworkEquilibriumCLS.LinearNash

theorem solution {n : ℕ} (hn : 0 < n) (p : Quadratic n)
    (z : CombinedIndex p → ℝ) :
    FunctionKKT (affineValue p) z ↔
      IntervalKKT (mixedLower p) (fun _ => 1) (combinedValue p) (affinePoint p z) := by
  classical
  -- how a single-coordinate update passes through the affine substitution
  have hupd_l : ∀ (i : Fin n) (t : ℝ),
      affinePoint p (Function.update z (.inl i) t)
        = Function.update (affinePoint p z) (.inl i) t := by
    intro i t; funext b
    rcases b with b | b
    · by_cases h : b = i
      · subst h; simp [affinePoint]
      · simp [affinePoint, Function.update_of_ne (show (Sum.inl b : CombinedIndex p) ≠ .inl i by simpa using h)]
    · simp [affinePoint]
  have hupd_r : ∀ (a : Auxiliary p) (t : ℝ),
      affinePoint p (Function.update z (.inr a) t)
        = Function.update (affinePoint p z) (.inr a) (2 * t - 1) := by
    intro a t; funext b
    rcases b with b | b
    · simp [affinePoint]
    · by_cases h : b = a
      · subst h; simp [affinePoint]
      · simp [affinePoint, Function.update_of_ne (show (Sum.inr b : CombinedIndex p) ≠ .inr a by simpa using h)]
  have hpl : ∀ i : Fin n, coordinatePartial (affineValue p) z (.inl i)
      = coordinatePartial (combinedValue p) (affinePoint p z) (.inl i) := by
    intro i
    simp only [coordinatePartial, affineValue, hupd_l]
    rfl
  have hpr : ∀ a : Auxiliary p, coordinatePartial (affineValue p) z (.inr a)
      = 2 * coordinatePartial (combinedValue p) (affinePoint p z) (.inr a) := by
    intro a
    simp only [coordinatePartial, affineValue, hupd_r]
    set g : ℝ → ℝ := fun s => combinedValue p (Function.update (affinePoint p z) (.inr a) s)
    show deriv (fun t : ℝ => g (2 * t - 1)) (z (.inr a)) = 2 * deriv g (affinePoint p z (.inr a))
    have h1 := deriv_comp_mul_left (2 : ℝ) (fun x => g (x - 1)) (z (.inr a))
    have h2 : deriv (fun x => g (x - 1)) (2 * z (.inr a)) = deriv g (2 * z (.inr a) - 1) :=
      deriv_comp_sub_const (f := g) (a := 1) (x := 2 * z (.inr a))
    simp only [smul_eq_mul] at h1
    rw [h1, h2]
    simp [affinePoint]
  constructor
  · rintro ⟨hcube, hsign⟩
    refine ⟨fun b => ?_, fun b => ?_⟩
    · rcases b with i | a
      · simpa [mixedLower, affinePoint] using hcube (.inl i)
      · have := hcube (.inr a)
        simp only [mixedLower, affinePoint]
        constructor <;> linarith [this.1, this.2]
    · rcases b with i | a
      · have := hsign (.inl i)
        simp only [mixedLower, affinePoint, ← hpl, neg_zero] at this ⊢
        exact this
      · have := hsign (.inr a)
        simp only [mixedLower, affinePoint]
        rw [hpr] at this
        constructor
        · intro h; have := this.1 (by linarith); linarith
        · intro h; have := this.2 (by linarith); linarith
  · rintro ⟨hbox, hsign⟩
    refine ⟨fun b => ?_, fun b => ?_⟩
    · rcases b with i | a
      · simpa [mixedLower, affinePoint] using hbox (.inl i)
      · have := hbox (.inr a)
        simp only [mixedLower, affinePoint] at this
        constructor <;> linarith [this.1, this.2]
    · rcases b with i | a
      · have := hsign (.inl i)
        simp only [mixedLower, affinePoint, ← hpl, neg_zero] at this ⊢
        exact this
      · have := hsign (.inr a)
        simp only [mixedLower, affinePoint] at this
        rw [hpr]
        constructor
        · intro h; have := this.1 (by linarith); linarith
        · intro h; have := this.2 (by linarith); linarith
