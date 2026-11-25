-- Prove2me | solution 2 for PauliMatrix.IsAnticommuting.card_le_three
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T19:36:56.081903+00:00
-- url     : https://prove2.me/submissions/4a56509a-1b98-4573-b40a-5cd471e39b97

import Mathlib
import Definitions.Def_minkowskiMatrix
import Definitions.Def_FermionDirac_IsCliffordFamily
import Definitions.Def_PauliMatrix_IsAnticommuting
import Definitions.Def_FermionDirac_gamma

open Matrix Complex

namespace S69D

lemma tr_zero {ι : Type*} {n : ℕ} {τ : ι → Matrix (Fin n) (Fin n) ℂ}
    (hsq : ∀ a, τ a * τ a = 1) (hac : ∀ a b, a ≠ b → τ a * τ b = -(τ b * τ a))
    (a b : ι) (hab : a ≠ b) : (τ a).trace = 0 := by
  have h1 : (τ a).trace = (τ a * τ b * τ b).trace := by rw [mul_assoc, hsq, mul_one]
  have h2 : (τ a * τ b * τ b).trace = (τ b * τ a * τ b).trace := by
    rw [Matrix.trace_mul_comm, ← mul_assoc]
  have h3 : (τ b * τ a * τ b).trace = -(τ a).trace := by
    rw [hac b a (Ne.symm hab), neg_mul, Matrix.trace_neg, mul_assoc, hsq, mul_one]
  have : (τ a).trace = -(τ a).trace := h1.trans (h2.trans h3)
  linear_combination this / 2

lemma tr_mul_zero {ι : Type*} {n : ℕ} {τ : ι → Matrix (Fin n) (Fin n) ℂ}
    (hac : ∀ a b, a ≠ b → τ a * τ b = -(τ b * τ a))
    (a b : ι) (hab : a ≠ b) : (τ a * τ b).trace = 0 := by
  have : (τ a * τ b).trace = -(τ a * τ b).trace := by
    conv_lhs => rw [Matrix.trace_mul_comm, hac b a (Ne.symm hab)]
    rw [Matrix.trace_neg]
  linear_combination this / 2

lemma li {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] {n : ℕ} (hn : n ≠ 0)
    {τ : ι → Matrix (Fin n) (Fin n) ℂ}
    (hsq : ∀ a, τ a * τ a = 1) (hac : ∀ a b, a ≠ b → τ a * τ b = -(τ b * τ a)) :
    LinearIndependent ℂ (fun o : Option ι => o.elim (1 : Matrix (Fin n) (Fin n) ℂ) τ) := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have htr : ∀ a, (τ a).trace = 0 := fun a => by
    obtain ⟨b, hb⟩ := exists_ne a
    exact tr_zero hsq hac a b hb.symm
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fintype.sum_option] at hg
  simp only [Option.elim] at hg
  have h0 : g none = 0 := by
    have := congrArg Matrix.trace hg
    simp only [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_sum, htr, smul_zero,
      Finset.sum_const_zero, add_zero, Matrix.trace_one, Fintype.card_fin, Matrix.trace_zero,
      smul_eq_mul] at this
    simp only [mul_zero, Finset.sum_const_zero, add_zero] at this
    exact (mul_eq_zero.mp this).resolve_right hn'
  intro o
  rcases o with _ | b
  · exact h0
  · have := congrArg (fun M => Matrix.trace (M * τ b)) hg
    simp only [add_mul, Matrix.trace_add, smul_mul_assoc, one_mul, Matrix.trace_smul, htr,
      smul_zero, zero_add, Finset.sum_mul, Matrix.trace_sum, zero_mul, Matrix.trace_zero] at this
    rw [Finset.sum_eq_single b] at this
    · rw [hsq, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at this
      exact (mul_eq_zero.mp this).resolve_right hn'
    · intro a _ hab; rw [tr_mul_zero hac a b hab, smul_zero]
    · intro h; exact absurd (Finset.mem_univ b) h

lemma card_le {ι : Type*} [Fintype ι] [DecidableEq ι] [Nontrivial ι] {n : ℕ} (hn : n ≠ 0)
    {τ : ι → Matrix (Fin n) (Fin n) ℂ}
    (hsq : ∀ a, τ a * τ a = 1) (hac : ∀ a b, a ≠ b → τ a * τ b = -(τ b * τ a)) :
    Fintype.card ι + 1 ≤ n * n := by
  have := (li hn hsq hac).fintype_card_le_finrank
  simpa [Module.finrank_matrix] using this

lemma anti_of {ι : Type*} [DecidableEq ι] {τ : ι → Matrix (Fin 2) (Fin 2) ℂ}
    (hτ : PauliMatrix.IsAnticommuting τ) :
    (∀ a, τ a * τ a = 1) ∧ (∀ a b, a ≠ b → τ a * τ b = -(τ b * τ a)) := by
  constructor
  · intro a
    have := hτ a a
    simp only [if_pos rfl] at this
    have h2 : (2 : ℂ) • (τ a * τ a) = (2 : ℂ) • 1 := by rw [two_smul]; exact this
    exact smul_right_injective _ (two_ne_zero) h2
  · intro a b hab
    have := hτ a b
    rw [if_neg hab, zero_smul] at this
    exact eq_neg_of_add_eq_zero_left this

lemma mink (μ ν : Fin 1 ⊕ Fin 3) :
    (minkowskiMatrix μ ν : ℂ) = if μ = ν then Sum.elim (fun _ => (1:ℂ)) (fun _ => -1) μ else 0 := by
  rcases μ with i | i <;> rcases ν with j | j <;>
    simp [minkowskiMatrix, LieAlgebra.Orthogonal.indefiniteDiagonal, Matrix.diagonal_apply]
  all_goals split_ifs <;> simp

lemma cl_sq {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : Fermion.Dirac.IsCliffordFamily γ) (μ : Fin 1 ⊕ Fin 3) :
    γ μ * γ μ = (Sum.elim (fun _ => (1:ℂ)) (fun _ => -1) μ) • 1 := by
  have := hγ μ μ
  rw [mink, if_pos rfl, ← two_smul ℂ (γ μ * γ μ), mul_smul] at this
  exact smul_right_injective _ (two_ne_zero) this

lemma cl_ac {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : Fermion.Dirac.IsCliffordFamily γ) (μ ν : Fin 1 ⊕ Fin 3) (h : μ ≠ ν) :
    γ μ * γ ν = -(γ ν * γ μ) := by
  have := hγ μ ν
  rw [mink, if_neg h, mul_zero, zero_smul] at this
  exact eq_neg_of_add_eq_zero_left this

lemma inv_sq {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : Fermion.Dirac.IsCliffordFamily γ) (μ : Fin 1 ⊕ Fin 3) :
    Fermion.Dirac.IsCliffordFamily.involutions γ μ * Fermion.Dirac.IsCliffordFamily.involutions γ μ = 1 := by
  simp only [Fermion.Dirac.IsCliffordFamily.involutions, smul_mul_smul_comm, cl_sq hγ, smul_smul]
  rcases μ with i | i <;> simp

lemma inv_ac {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : Fermion.Dirac.IsCliffordFamily γ) (μ ν : Fin 1 ⊕ Fin 3) (h : μ ≠ ν) :
    Fermion.Dirac.IsCliffordFamily.involutions γ μ * Fermion.Dirac.IsCliffordFamily.involutions γ ν =
    -(Fermion.Dirac.IsCliffordFamily.involutions γ ν * Fermion.Dirac.IsCliffordFamily.involutions γ μ) := by
  simp only [Fermion.Dirac.IsCliffordFamily.involutions, smul_mul_smul_comm, cl_ac hγ μ ν h,
    smul_neg, mul_comm (Sum.elim (fun _ => (1:ℂ)) (fun _ => I) μ)]

lemma even' {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : Fermion.Dirac.IsCliffordFamily γ) : Even n := by
  have hac := cl_ac hγ (Sum.inl 0) (Sum.inr 0) (by simp)
  have h0 := cl_sq hγ (Sum.inl 0)
  have h1 := cl_sq hγ (Sum.inr 0)
  have hd0 : (γ (Sum.inl 0)).det ≠ 0 := by
    intro h; have := congrArg Matrix.det h0; simp [Matrix.det_mul, h, Matrix.det_neg] at this
  have hd1 : (γ (Sum.inr 0)).det ≠ 0 := by
    intro h; have := congrArg Matrix.det h1; simp [Matrix.det_mul, h, Matrix.det_neg] at this
    exact pow_ne_zero n (by norm_num) this.symm
  have := congrArg Matrix.det hac
  rw [Matrix.det_neg, Matrix.det_mul, Matrix.det_mul, Fintype.card_fin] at this
  have hp : ((-1 : ℂ) ^ n) = 1 := by
    have hne : (γ (Sum.inl 0)).det * (γ (Sum.inr 0)).det ≠ 0 := mul_ne_zero hd0 hd1
    apply mul_right_cancel₀ hne
    linear_combination -this
  exact (neg_one_pow_eq_one_iff_even (by norm_num)).mp hp

lemma ne_two' {n : ℕ} {γ : Fin 1 ⊕ Fin 3 → Matrix (Fin n) (Fin n) ℂ}
    (hγ : Fermion.Dirac.IsCliffordFamily γ) : n ≠ 2 := by
  intro h2
  haveI : Nontrivial (Fin 1 ⊕ Fin 3) := ⟨⟨Sum.inl 0, Sum.inr 0, by simp⟩⟩
  have := card_le (n := n) (by omega) (inv_sq hγ) (inv_ac hγ)
  simp at this
  subst h2; omega

end S69D

theorem solution {ι : Type*} [DecidableEq ι]
    {τ : ι → Matrix (Fin 2) (Fin 2) ℂ} (hτ : PauliMatrix.IsAnticommuting τ) [Fintype ι] :
    Fintype.card ι ≤ 3 := by
  obtain ⟨hsq, hac⟩ := S69D.anti_of hτ
  rcases subsingleton_or_nontrivial ι with h | h
  · have := Fintype.card_le_one_iff_subsingleton.mpr h; omega
  · have := S69D.card_le (n := 2) (by norm_num) hsq hac; omega
