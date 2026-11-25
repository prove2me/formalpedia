-- Prove2me | solution 1 for PauliMatrix.IsAnticommuting.linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @terra-mathbot
-- created : 2026-11-25T19:36:26.638382+00:00
-- url     : https://prove2.me/submissions/85ae1f49-6433-4efa-b7d5-0a1bbff245a3

import Mathlib
import Definitions.Def_PauliMatrix_IsAnticommuting

open Matrix

lemma pauli_sq {ι : Type*} [DecidableEq ι] {τ : ι → Matrix (Fin 2) (Fin 2) ℂ}
    (hτ : PauliMatrix.IsAnticommuting τ) (a : ι) : τ a * τ a = 1 := by
  have h := hτ a a
  rw [if_pos rfl, ← two_smul ℂ (τ a * τ a)] at h
  exact smul_right_injective _ two_ne_zero h

lemma pauli_anti {ι : Type*} [DecidableEq ι] {τ : ι → Matrix (Fin 2) (Fin 2) ℂ}
    (hτ : PauliMatrix.IsAnticommuting τ) {a b : ι} (h : a ≠ b) :
    τ a * τ b + τ b * τ a = 0 := by
  rw [hτ a b, if_neg h]; simp

lemma pauli_trace {ι : Type*} [DecidableEq ι] {τ : ι → Matrix (Fin 2) (Fin 2) ℂ}
    (hτ : PauliMatrix.IsAnticommuting τ) {a b : ι} (hab : b ≠ a) : (τ a).trace = 0 := by
  have hanti : τ b * τ a = -(τ a * τ b) := eq_neg_of_add_eq_zero_left (by
    rw [add_comm]; exact pauli_anti hτ hab.symm)
  have h1 : (τ a * (τ b * τ b)).trace = (τ a).trace := by
    rw [pauli_sq hτ, Matrix.mul_one]
  have h2 : (τ a * (τ b * τ b)).trace = -(τ a).trace := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hanti, Matrix.neg_mul,
      Matrix.trace_neg, Matrix.mul_assoc, pauli_sq hτ, Matrix.mul_one]
  linear_combination (h2 - h1) / 2

lemma pauli_trace_mul_ne {ι : Type*} [DecidableEq ι] {τ : ι → Matrix (Fin 2) (Fin 2) ℂ}
    (hτ : PauliMatrix.IsAnticommuting τ) {a b : ι} (h : a ≠ b) : (τ a * τ b).trace = 0 := by
  have := congrArg Matrix.trace (pauli_anti hτ h)
  rw [Matrix.trace_add, Matrix.trace_mul_comm (τ b), Matrix.trace_zero] at this
  linear_combination this / 2

lemma pauli_li {ι : Type*} [DecidableEq ι]
    {τ : ι → Matrix (Fin 2) (Fin 2) ℂ} (hτ : PauliMatrix.IsAnticommuting τ) [Fintype ι]
    [Nontrivial ι] :
    LinearIndependent ℂ (fun o : Option ι => o.elim (1 : Matrix (Fin 2) (Fin 2) ℂ) τ) := by
  set v : Option ι → Matrix (Fin 2) (Fin 2) ℂ := fun o => o.elim 1 τ with hv
  have htr0 : ∀ a, (τ a).trace = 0 := fun a => by
    obtain ⟨b, hb⟩ := exists_ne a
    exact pauli_trace hτ hb
  have htr : ∀ i j, (v i * v j).trace = if i = j then (2 : ℂ) else 0 := by
    intro i j
    rcases i with _ | a <;> rcases j with _ | b
    · simp [v]
    · simp [v, htr0]
    · simp [v, htr0]
    · by_cases h : a = b
      · subst h; simp [v, pauli_sq hτ]
      · simp [v, pauli_trace_mul_ne hτ h, h]
  rw [Fintype.linearIndependent_iff]
  intro g hg j
  have := congrArg (fun M => (M * v j).trace) hg
  simp only [Finset.sum_mul, Matrix.trace_sum, Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul,
    Matrix.zero_mul, Matrix.trace_zero, htr] at this
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at this
  simpa using this

theorem solution {ι : Type*} [DecidableEq ι]
    {τ : ι → Matrix (Fin 2) (Fin 2) ℂ} (hτ : PauliMatrix.IsAnticommuting τ) [Fintype ι] [Nontrivial ι] :
    LinearIndependent ℂ (fun o : Option ι => o.elim (1 : Matrix (Fin 2) (Fin 2) ℂ) τ) :=
  pauli_li hτ

