-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P56.normalized_choi_covariance
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T05:51:46.131085+00:00
-- url     : https://prove2.me/submissions/7d659931-e5ec-4cdb-a7d5-3e2f203bdd54

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P56

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Information100 QAlgorithms.Papers.Independent.Information100.P56

open scoped ComplexConjugate ComplexOrder Matrix

attribute [local instance] Classical.propDecidable

lemma h54b_single_conj {A : Type*} [Fintype A] [DecidableEq A] (Um : Matrix A A ℂ) (a c x y : A) :
    (Um * Matrix.single a c (1 : ℂ) * Umᴴ) x y = Um x a * star (Um y c) := by
  simp [Matrix.mul_apply, Matrix.single_apply, ite_and]

lemma h54b_choi_entry {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (N : QAlgorithms.Superop A B)
    (hlin : ∀ ρ : Matrix A A ℂ, N ρ = ∑ a, ∑ c, ρ a c • N (Matrix.single a c 1))
    (Um : Matrix A A ℂ) (Vm : Matrix B B ℂ) (a c : A) (b d : B) :
    (Matrix.kronecker Umᵀ Vmᴴ * normalizedChoi N * (Matrix.kronecker Umᵀ Vmᴴ)ᴴ) (a, b) (c, d) =
      (Vmᴴ * N (Um * Matrix.single a c 1 * Umᴴ) * Vm) b d / (Fintype.card A : ℂ) := by
  rw [hlin (Um * Matrix.single a c 1 * Umᴴ)]
  simp only [h54b_single_conj]
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.kroneckerMap_apply, Matrix.transpose_apply, normalizedChoi, Fintype.sum_prod_type,
    Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, Matrix.kronecker, star_mul', star_star,
    Finset.sum_div, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun _ _ => ?_)
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun _ _ => Finset.sum_congr rfl (fun _ _ =>
    Finset.sum_congr rfl (fun _ _ => ?_)))
  ring

theorem solution
    {G A B : Type*} [Fintype A] [DecidableEq A] [Nonempty A]
    [Fintype B] [DecidableEq B] [Nonempty B]
    (N : QAlgorithms.Superop A B) (hN : QAlgorithms.IsChannel N)
    (U : G → Matrix.unitaryGroup A ℂ) (V : G → Matrix.unitaryGroup B ℂ)
    : ∀ g,
      let J := normalizedChoi N
      let R := Matrix.kronecker (U g : Matrix A A ℂ)ᵀ (V g : Matrix B B ℂ)ᴴ
      let C := Matrix.kronecker (fun i j => conj ((U g : Matrix A A ℂ) i j))
        (V g : Matrix B B ℂ)
      ((∀ rho, N ((U g : Matrix A A ℂ) * rho * (U g : Matrix A A ℂ)ᴴ) =
        (V g : Matrix B B ℂ) * N rho * (V g : Matrix B B ℂ)ᴴ) ↔ J = R * J * Rᴴ) ∧
      (J = R * J * Rᴴ ↔ Commute J C) := by
  intro g J R C
  obtain ⟨m, E, -, hNE⟩ := hN
  set Um : Matrix A A ℂ := (U g : Matrix A A ℂ) with hUm
  set Vm : Matrix B B ℂ := (V g : Matrix B B ℂ) with hVm
  have hU := (U g).2
  have hV := (V g).2
  have hUU : Umᴴ * Um = 1 := Unitary.star_mul_self_of_mem hU
  have hVV : Vmᴴ * Vm = 1 := Unitary.star_mul_self_of_mem hV
  have hVV' : Vm * Vmᴴ = 1 := Unitary.mul_star_self_of_mem hV
  -- linearity
  let Lmap : Matrix A A ℂ →ₗ[ℂ] Matrix B B ℂ :=
    { toFun := N
      map_add' := by
        intro X Y
        rw [hNE, hNE X, hNE Y]
        unfold QAlgorithms.krausApply
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := by
        intro c X
        rw [hNE, hNE X]
        unfold QAlgorithms.krausApply
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        simp [Matrix.mul_smul, Matrix.smul_mul] }
  have hL : ∀ X, N X = Lmap X := fun X => rfl
  have hexp : ∀ ρ : Matrix A A ℂ, ρ = ∑ a, ∑ c, ρ a c • Matrix.single a c (1 : ℂ) := by
    intro ρ
    conv_lhs => rw [Matrix.matrix_eq_sum_single ρ]
    simp [Matrix.smul_single]
  have hlin : ∀ ρ : Matrix A A ℂ, N ρ = ∑ a, ∑ c, ρ a c • N (Matrix.single a c 1) := by
    intro ρ
    conv_lhs => rw [hexp ρ]
    rw [hL, map_sum]
    simp only [map_sum, map_smul]
    rfl
  have hent := h54b_choi_entry N hlin Um Vm
  have hcardne : (Fintype.card A : ℂ) ≠ 0 := by
    have := Fintype.card_pos (α := A)
    exact_mod_cast this.ne'
  have hRR : R * Rᴴ = 1 ∧ Rᴴ * R = 1 := by
    have hT : Umᵀ ∈ Matrix.unitaryGroup A ℂ := Matrix.transpose_mem_unitaryGroup_iff.mpr hU
    have hS : Vmᴴ ∈ Matrix.unitaryGroup B ℂ := by
      rw [← Matrix.star_eq_conjTranspose]; exact Unitary.star_mem hV
    have hk := Matrix.kronecker_mem_unitary hT hS
    exact ⟨Unitary.mul_star_self_of_mem hk, Unitary.star_mul_self_of_mem hk⟩
  have hC : C = Rᴴ := by
    ext ⟨a, b⟩ ⟨c, d⟩
    simp only [C, R, Matrix.kronecker, Matrix.kroneckerMap_apply, Matrix.transpose_apply,
      Matrix.conjTranspose_apply]
    show conj ((U g : Matrix A A ℂ) a c) * (V g : Matrix B B ℂ) b d = _
    simp
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro hcov
    ext ⟨a, b⟩ ⟨c, d⟩
    rw [hent, hcov]
    have : Vmᴴ * (Vm * N (Matrix.single a c 1) * Vmᴴ) * Vm = N (Matrix.single a c 1) := by
      rw [show Vmᴴ * (Vm * N (Matrix.single a c 1) * Vmᴴ) * Vm =
        (Vmᴴ * Vm) * N (Matrix.single a c 1) * (Vmᴴ * Vm) by simp only [Matrix.mul_assoc]]
      rw [hVV, Matrix.one_mul, Matrix.mul_one]
    rw [this]
    rfl
  · intro hJ ρ
    have h1 : ∀ a c, N (Um * Matrix.single a c 1 * Umᴴ) = Vm * N (Matrix.single a c 1) * Vmᴴ := by
      intro a c
      have h2 : Vmᴴ * N (Um * Matrix.single a c 1 * Umᴴ) * Vm = N (Matrix.single a c 1) := by
        ext b d
        have := congrFun (congrFun hJ (a, b)) (c, d)
        rw [hent] at this
        simp only [J, normalizedChoi] at this
        exact ((div_left_inj' hcardne).mp this).symm
      rw [← h2]
      rw [show Vm * (Vmᴴ * N (Um * Matrix.single a c 1 * Umᴴ) * Vm) * Vmᴴ =
        (Vm * Vmᴴ) * N (Um * Matrix.single a c 1 * Umᴴ) * (Vm * Vmᴴ) by simp only [Matrix.mul_assoc]]
      rw [hVV', Matrix.one_mul, Matrix.mul_one]
    have e : Um * ρ * Umᴴ = ∑ a, ∑ c, ρ a c • (Um * Matrix.single a c 1 * Umᴴ) := by
      conv_lhs => rw [hexp ρ]
      simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
    rw [e, hL, map_sum]
    simp only [map_sum, map_smul]
    simp only [← hL, h1]
    rw [hlin ρ]
    simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hC]
    constructor
    · intro hJ
      show J * Rᴴ = Rᴴ * J
      conv_rhs => rw [hJ]
      rw [show Rᴴ * (R * J * Rᴴ) = (Rᴴ * R) * J * Rᴴ by simp only [Matrix.mul_assoc], hRR.2,
        Matrix.one_mul]
    · intro hc
      have hc' : J * Rᴴ = Rᴴ * J := hc
      rw [Matrix.mul_assoc, hc', ← Matrix.mul_assoc, hRR.1, Matrix.one_mul]
