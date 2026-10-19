-- Prove2me | solution 1 for QAlgorithms.Nannicini.maxCut_hamiltonian_structure
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T10:35:33.061897+00:00
-- url     : https://prove2.me/submissions/e0faa358-1dd7-4495-8152-ee8b2d12385b

import Definitions.Def_QAlgorithms_Nannicini_Ch08b_Model
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false

open QAlgorithms QAlgorithms.SDP

private lemma subgradient_parts {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (γ ε e : ℝ) (f : Fin n → ℝ) :
    ∃ (a : ℝ) (d : Fin n → ℂ), 0 ≤ a ∧ a ≤ 1 ∧
      (∀ j, ‖d j‖ ≤ 1 - a) ∧
      maxCutSubgrad C γ ε e f = -(a : ℂ) • cHat C + Matrix.diagonal d := by
  classical
  unfold maxCutSubgrad
  split_ifs with h0 h1
  · exact ⟨0, 0, by norm_num, by norm_num, by simp, by simp⟩
  · exact ⟨1, 0, by norm_num, by norm_num, by simp, by simp⟩
  · refine ⟨0, (fun j => if (n : ℝ)⁻¹ < f j then 1 else if f j < (n : ℝ)⁻¹ then -1 else 0), by norm_num, by norm_num, ?_, by simp⟩
    intro j
    dsimp only
    split_ifs <;> norm_num

private lemma accumulate_parts {n : ℕ} (C : Matrix (Fin n) (Fin n) ℂ)
    (G : ℕ → Matrix (Fin n) (Fin n) ℂ) (s : Finset ℕ)
    (hG : ∀ τ, ∃ (a : ℝ) (d : Fin n → ℂ), 0 ≤ a ∧ a ≤ 1 ∧
      (∀ j, ‖d j‖ ≤ 1 - a) ∧ G τ = -(a : ℂ) • C + Matrix.diagonal d) :
    ∃ (A B : ℝ) (d : Fin n → ℂ), 0 ≤ A ∧ 0 ≤ B ∧ A + B = s.card ∧
      (∀ j, ‖d j‖ ≤ 1) ∧
      ∑ τ ∈ s, G τ = -(A : ℂ) • C + (B : ℂ) • Matrix.diagonal d := by
  classical
  choose a d ha hb hd heq using hG
  let A : ℝ := ∑ τ ∈ s, a τ
  let B : ℝ := (s.card : ℝ) - A
  let v : Fin n → ℂ := fun j => ∑ τ ∈ s, d τ j
  have hA : 0 ≤ A := Finset.sum_nonneg fun τ _ => ha τ
  have hAc : A ≤ s.card := by
    simpa using Finset.sum_le_sum (fun τ (_ : τ ∈ s) => hb τ)
  have hB : 0 ≤ B := sub_nonneg.mpr hAc
  have hv (j) : ‖v j‖ ≤ B := by
    calc
      ‖v j‖ ≤ ∑ τ ∈ s, ‖d τ j‖ := norm_sum_le _ _
      _ ≤ ∑ τ ∈ s, (1 - a τ) := Finset.sum_le_sum fun τ _ => hd τ j
      _ = B := by simp [B, A, Finset.sum_sub_distrib]
  have hsum : ∑ τ ∈ s, G τ = -(A : ℂ) • C + Matrix.diagonal v := by
    simp_rw [heq, Finset.sum_add_distrib]
    congr 1
    · simp [A, ← Finset.sum_smul, -Complex.ofReal_sum, Finset.sum_neg_distrib]
    · ext i j
      by_cases h : i = j
      · subst j; simp [v, Matrix.sum_apply]
      · simp [Matrix.sum_apply, Matrix.diagonal, h]
  refine ⟨A, B, fun j => (B : ℂ)⁻¹ * v j, hA, hB, by dsimp [B]; ring, ?_, ?_⟩
  · intro j
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hB]
    by_cases hB0 : B = 0
    · simp [hB0]
    · exact (mul_le_mul_of_nonneg_left (hv j) (inv_nonneg.mpr hB)).trans_eq
        (inv_mul_cancel₀ hB0)
  · rw [hsum]
    congr 1
    ext i j
    by_cases hij : i = j
    · subst j
      simp only [Matrix.diagonal_apply_eq, Matrix.smul_apply, smul_eq_mul]
      by_cases hB0 : B = 0
      · have hz : v i = 0 := norm_eq_zero.mp (le_antisymm ((hv i).trans (by simp [hB0])) (norm_nonneg _))
        simp [hB0, hz]
      · rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hB0), one_mul]
    · simp [Matrix.diagonal, hij]

private lemma iteration_budget (ε L : ℝ) (hε : 0 < ε) (t : ℕ)
    (ht1 : 1 ≤ t) (htT : t ≤ ⌈64 * (ε ^ 2)⁻¹ * L⌉₊) :
    (ε * 16⁻¹) * ((t - 1 : ℕ) : ℝ) ≤ 4 * ε⁻¹ * L := by
  have hx : 0 < 64 * (ε ^ 2)⁻¹ * L := by
    exact Nat.ceil_pos.mp (by omega)
  have ht : ((t - 1 : ℕ) : ℝ) ≤ 64 * (ε ^ 2)⁻¹ * L := by
    have hceil := Nat.ceil_lt_add_one hx.le
    have ht' : (t : ℝ) ≤ (⌈64 * (ε ^ 2)⁻¹ * L⌉₊ : ℝ) := by exact_mod_cast htT
    rw [Nat.cast_sub ht1, Nat.cast_one]
    linarith
  calc
    (ε * 16⁻¹) * ((t - 1 : ℕ) : ℝ) ≤ (ε * 16⁻¹) * (64 * (ε ^ 2)⁻¹ * L) :=
      mul_le_mul_of_nonneg_left ht (by positivity)
    _ = 4 * ε⁻¹ * L := by field_simp; ring

theorem solution {n : ℕ} (C : Matrix (Fin n) (Fin n) ℝ) (_hC : C.IsSymm)
    (_hC0 : C ≠ 0) (γ : ℝ) (_hγ : γ ∈ Set.Icc (-1 : ℝ) 1) (ε : ℝ) (hε : 0 < ε)
    (estC : ℕ → ℝ) (estD : ℕ → Fin n → ℝ)
    (_hest : ∀ τ, 1 ≤ τ → τ < ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊ →
      |estC τ - (cHat (C.map ((↑) : ℝ → ℂ)) *
          mmwuIterate (ε * 16⁻¹)
            (fun σ => maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC σ) (estD σ)) τ).trace.re|
          ≤ ε * 4⁻¹ ∧
        ∑ j, |estD τ j - (mmwuIterate (ε * 16⁻¹)
            (fun σ => maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC σ) (estD σ)) τ j j).re|
          ≤ ε * 4⁻¹)
    (t : ℕ) (ht1 : 1 ≤ t) (htT : t ≤ ⌈64 * (ε ^ 2)⁻¹ * Real.logb 2 n⌉₊) :
    ∃ (y : Fin 2 → ℝ) (d : Fin n → ℂ), (∀ j, ‖d j‖ ≤ 1) ∧
      -((ε * 16⁻¹ : ℝ) : ℂ) • ∑ τ ∈ Finset.Ico 1 t,
          maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC τ) (estD τ) =
        ((y 0 : ℝ) : ℂ) • cHat (C.map ((↑) : ℝ → ℂ)) + ((y 1 : ℝ) : ℂ) • Matrix.diagonal d ∧
      |y 0| + |y 1| ≤ 4 * ε⁻¹ * Real.logb 2 n := by
  classical
  obtain ⟨A, B, d, hA, hB, hAB, hd, hsum⟩ := accumulate_parts
    (cHat (C.map ((↑) : ℝ → ℂ)))
    (fun τ => maxCutSubgrad (C.map ((↑) : ℝ → ℂ)) γ ε (estC τ) (estD τ))
    (Finset.Ico 1 t)
    (fun τ => subgradient_parts _ γ ε (estC τ) (estD τ))
  let η : ℝ := ε * 16⁻¹
  refine ⟨![η * A, -η * B], d, hd, ?_, ?_⟩
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hsum, smul_add, smul_smul, smul_smul]
    simp only [η, Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_inv, Complex.ofReal_ofNat]
    congr 1; congr 1; ring
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    have hη : 0 ≤ η := by dsimp [η]; positivity
    rw [abs_of_nonneg (mul_nonneg hη hA), abs_of_nonpos (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hη) hB)]
    have hcard : (Finset.Ico 1 t).card = t - 1 := by simp
    have heq : η * A + -(-η * B) = η * ((t - 1 : ℕ) : ℝ) := by
      rw [← hcard, ← hAB]; ring
    rw [heq]
    exact iteration_budget ε (Real.logb 2 n) hε t ht1 htT
