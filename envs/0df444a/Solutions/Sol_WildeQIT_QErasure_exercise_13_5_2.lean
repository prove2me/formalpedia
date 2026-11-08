-- Prove2me | solution 1 for WildeQIT.QErasure.exercise_13_5_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T23:58:19.297297+00:00
-- url     : https://prove2.me/submissions/ecb797a7-72fd-4d9e-b530-27a8a02fc1f3

import Mathlib
import Definitions.Def_WildeQIT_Degradable_IsDegradable
import Definitions.Def_WildeQIT_QErasure_erasureChannel

open Matrix

open WildeQIT WildeQIT.Degradable WildeQIT.QErasure in
theorem solution (a : Type) [Fintype a] [DecidableEq a] [Nonempty a] (ε : ℝ) (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) (hε : ε ≤ 1 / 2) :
    WildeQIT.Degradable.IsDegradable (erasureChannel a ε h0 h1) := by
  classical
  have hε1 : 0 < 1 - ε := by linarith
  set p : ℝ := ε / (1 - ε) with hp
  have hp0 : 0 ≤ p := div_nonneg h0 hε1.le
  have hp1 : p ≤ 1 := by rw [hp, div_le_one hε1]; linarith
  have hpe : (p : ℂ) * (1 - (ε : ℂ)) = ε := by
    have : p * (1 - ε) = ε := by rw [hp]; field_simp
    exact_mod_cast this
  have hz1 : ∀ z : ℂ, ((Real.sqrt (1 - ε) : ℝ) : ℂ) * z * ((Real.sqrt (1 - ε) : ℝ) : ℂ) =
      (1 - (ε : ℂ)) * z := by
    intro z
    have : ((Real.sqrt (1 - ε) : ℝ) : ℂ) * ((Real.sqrt (1 - ε) : ℝ) : ℂ) = 1 - (ε : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hε1.le]; push_cast; ring
    linear_combination z * this
  have hz2 : ∀ z : ℂ, ((Real.sqrt ε : ℝ) : ℂ) * z * ((Real.sqrt ε : ℝ) : ℂ) = (ε : ℂ) * z := by
    intro z
    have : ((Real.sqrt ε : ℝ) : ℂ) * ((Real.sqrt ε : ℝ) : ℂ) = (ε : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
    linear_combination z * this
  have hz3 : ∀ z : ℂ, ((Real.sqrt p : ℝ) : ℂ) * z * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) * z := by
    intro z
    have : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
    linear_combination z * this
  have hz4 : ∀ z : ℂ, ((Real.sqrt (1 - p) : ℝ) : ℂ) * z * ((Real.sqrt (1 - p) : ℝ) : ℂ) =
      (1 - (p : ℂ)) * z := by
    intro z
    have : ((Real.sqrt (1 - p) : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ) = 1 - (p : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
    linear_combination z * this
  have hsq3 : ((Real.sqrt p : ℝ) : ℂ) * ((Real.sqrt p : ℝ) : ℂ) = (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt hp0]
  have hsq4 : ((Real.sqrt (1 - p) : ℝ) : ℂ) * ((Real.sqrt (1 - p) : ℝ) : ℂ) = 1 - (p : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]; push_cast; ring
  -- Kraus operators of the erasure channel, written over `Option a`
  let Kn : Option a → Matrix (Option a) a ℂ := fun k => match k with
    | none => Matrix.of fun y x => if y = some x then ((Real.sqrt (1 - ε) : ℝ) : ℂ) else 0
    | some i => Matrix.of fun y x => if y = none ∧ x = i then ((Real.sqrt ε : ℝ) : ℂ) else 0
  -- Kraus operators of the degrading channel
  let Kd : Option (Option a) → Matrix (Option a) (Option a) ℂ := fun k => match k with
    | none => Matrix.of fun y x => if y = x ∧ x ≠ none then ((Real.sqrt p : ℝ) : ℂ) else 0
    | some none => Matrix.of fun y x => if y = none ∧ x = none then 1 else 0
    | some (some i) => Matrix.of fun y x =>
        if y = none ∧ x = some i then ((Real.sqrt (1 - p) : ℝ) : ℂ) else 0
  have hcomplete : ∑ k, (Kd k)ᴴ * Kd k = 1 := by
    ext x x'
    simp only [Matrix.sum_apply, Fintype.sum_option, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.of_apply, Kd]
    rcases x with _ | x <;> rcases x' with _ | x'
    · simp
    · simp
    · simp
    · by_cases hx : x = x'
      · subst hx
        simp [apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq]
        linear_combination hsq3 + hsq4
      · simp [hx, Ne.symm hx, apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq]
  let D : QChannel (Option a) (Option a) :=
    { ι := Option (Option a), K := Kd, complete := hcomplete }
  refine ⟨D, fun ρ _ => ?_⟩
  -- closed forms
  set Nρ : Matrix (Option a) (Option a) ℂ := ∑ k : Option a, Kn k * ρ * (Kn k)ᴴ with hNρ
  have hC : complementaryApply (erasureChannel a ε h0 h1) ρ =
      (Matrix.of fun k l : Option a => ∑ y : Option a, ∑ x' : a,
        (∑ x : a, Kn k y x * ρ x x') * star (Kn l y x') :
        Matrix (Option a) (Option a) ℂ) := by
    ext k l
    simp only [complementaryApply, partialTraceLeft, isometricExtension, Matrix.of_apply,
      Matrix.mul_apply, Matrix.conjTranspose_apply]
    rfl
  have hDapp : ∀ σ : Matrix (Option a) (Option a) ℂ,
      D.apply σ = ∑ k : Option (Option a), Kd k * σ * (Kd k)ᴴ := fun σ => rfl
  have hgoal : (Matrix.of fun k l : Option a => ∑ y : Option a, ∑ x' : a,
        (∑ x : a, Kn k y x * ρ x x') * star (Kn l y x') : Matrix (Option a) (Option a) ℂ) =
      ∑ k : Option (Option a), Kd k * Nρ * (Kd k)ᴴ := by
    -- entries of N ρ
    have hNss : ∀ x x', Nρ (some x) (some x') = (1 - (ε : ℂ)) * ρ x x' := by
      intro x x'
      simp only [hNρ, Kn, Matrix.sum_apply, Matrix.add_apply, Fintype.sum_option,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      simp [apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, hz1]
    have hNnn : Nρ none none = (ε : ℂ) * ∑ x, ρ x x := by
      simp only [hNρ, Kn, Matrix.sum_apply, Matrix.add_apply, Fintype.sum_option,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      simp [apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, hz2, Finset.mul_sum]
    have hNsn : ∀ x, Nρ (some x) none = 0 := by
      intro x
      simp only [hNρ, Kn, Matrix.sum_apply, Matrix.add_apply, Fintype.sum_option,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      simp [apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and]
    have hNns : ∀ x, Nρ none (some x) = 0 := by
      intro x
      simp only [hNρ, Kn, Matrix.sum_apply, Matrix.add_apply, Fintype.sum_option,
        Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply]
      simp [apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and]
    ext k l
    simp only [Matrix.of_apply, Kn, Kd, Matrix.sum_apply, Fintype.sum_option, Matrix.mul_apply,
      Matrix.conjTranspose_apply]
    rcases k with _ | k <;> rcases l with _ | l
    · simp [apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, hz1, hz4,
        hNnn, hNss, Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      linear_combination (ρ x x) * hpe
    · simp [apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, hNns, hNsn]
    · simp [apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, hNns, hNsn]
    · simp [apply_ite star, Finset.sum_ite_eq', Finset.sum_ite_eq, ite_and, hz2, hz3, hNss]
      linear_combination (-(ρ k l)) * hpe
  rw [hC]
  exact hgoal
