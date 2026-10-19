-- Prove2me | solution 1 for Williamson_of_sequences
-- status  : ACCEPTED   (prove)
-- author  : @ronr
-- created : 2026-09-06T00:58:22.312982+00:00
-- url     : https://prove2.me/submissions/b3c6aebf-a362-4eaf-9e17-5f9b2cd3a3cf

import Mathlib
import Theorems.Thm_Williamson_array

open Matrix

/-- Transport a `±1`-entried orthogonal matrix across an index equivalence. -/
private lemma transport_hadamard {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ']
    [DecidableEq κ'] (e : κ' ≃ κ) (M : Matrix κ κ ℝ) (c : ℝ)
    (hpm : ∀ i j, M i j = 1 ∨ M i j = -1)
    (horth : M * Mᵀ = c • (1 : Matrix κ κ ℝ)) :
    (∀ i j, (M.submatrix e e) i j = 1 ∨ (M.submatrix e e) i j = -1) ∧
      (M.submatrix e e) * (M.submatrix e e)ᵀ = c • (1 : Matrix κ' κ' ℝ) := by
  refine ⟨fun i j => hpm (e i) (e j), ?_⟩
  apply Matrix.ext
  intro i j
  have hlhs : ((M.submatrix e e) * (M.submatrix e e)ᵀ) i j = (M * Mᵀ) (e i) (e j) := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.submatrix_apply]
    exact Equiv.sum_comp e (fun l => M (e i) l * M (e j) l)
  rw [hlhs, horth]
  simp only [Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  by_cases h : i = j
  · subst h; simp
  · have hne : e i ≠ e j := fun heq => h (e.injective heq)
    simp [h, hne]

/-- **W3. Williamson matrices from sequences.** Four symmetric `±1` sequences of length `t`
whose periodic autocorrelations sum to zero give a Hadamard matrix of order `4t`. -/
theorem solution (t : ℕ) [NeZero t] (a b c d : ZMod t → ℝ)
    (hapm : ∀ i, a i = 1 ∨ a i = -1) (hbpm : ∀ i, b i = 1 ∨ b i = -1)
    (hcpm : ∀ i, c i = 1 ∨ c i = -1) (hdpm : ∀ i, d i = 1 ∨ d i = -1)
    (hasy : ∀ i, a (-i) = a i) (hbsy : ∀ i, b (-i) = b i)
    (hcsy : ∀ i, c (-i) = c i) (hdsy : ∀ i, d (-i) = d i)
    (hauto : ∀ i : ZMod t, (∑ j : ZMod t,
        (a (i - j) * a j + b (i - j) * b j + c (i - j) * c j + d (i - j) * d j)) =
      if i = 0 then (4 * t : ℝ) else 0) :
    ∃ M : Matrix (Fin (4 * t)) (Fin (4 * t)) ℝ,
      (∀ i j, M i j = 1 ∨ M i j = -1) ∧
        M * Mᵀ = ((4 * t : ℕ) : ℝ) • (1 : Matrix (Fin (4 * t)) (Fin (4 * t)) ℝ) := by
  have hcardZ : Fintype.card (ZMod t) = t := ZMod.card t
  set A := Matrix.circulant a with hAdef
  set B := Matrix.circulant b with hBdef
  set C := Matrix.circulant c with hCdef
  set D := Matrix.circulant d with hDdef
  have hApm : ∀ i j, A i j = 1 ∨ A i j = -1 := by
    intro i j; rw [hAdef, Matrix.circulant_apply]; exact hapm _
  have hBpm : ∀ i j, B i j = 1 ∨ B i j = -1 := by
    intro i j; rw [hBdef, Matrix.circulant_apply]; exact hbpm _
  have hCpm : ∀ i j, C i j = 1 ∨ C i j = -1 := by
    intro i j; rw [hCdef, Matrix.circulant_apply]; exact hcpm _
  have hDpm : ∀ i j, D i j = 1 ∨ D i j = -1 := by
    intro i j; rw [hDdef, Matrix.circulant_apply]; exact hdpm _
  have hAs : Aᵀ = A := by rw [hAdef]; exact Matrix.circulant_isSymm_iff.mpr hasy
  have hBs : Bᵀ = B := by rw [hBdef]; exact Matrix.circulant_isSymm_iff.mpr hbsy
  have hCs : Cᵀ = C := by rw [hCdef]; exact Matrix.circulant_isSymm_iff.mpr hcsy
  have hDs : Dᵀ = D := by rw [hDdef]; exact Matrix.circulant_isSymm_iff.mpr hdsy
  have hAB : A * B = B * A := by rw [hAdef, hBdef]; exact Matrix.circulant_mul_comm a b
  have hAC : A * C = C * A := by rw [hAdef, hCdef]; exact Matrix.circulant_mul_comm a c
  have hAD : A * D = D * A := by rw [hAdef, hDdef]; exact Matrix.circulant_mul_comm a d
  have hBC : B * C = C * B := by rw [hBdef, hCdef]; exact Matrix.circulant_mul_comm b c
  have hBD : B * D = D * B := by rw [hBdef, hDdef]; exact Matrix.circulant_mul_comm b d
  have hCD : C * D = D * C := by rw [hCdef, hDdef]; exact Matrix.circulant_mul_comm c d
  have hone : (1 : Matrix (ZMod t) (ZMod t) ℝ) =
      Matrix.circulant (fun i => if i = 0 then (1 : ℝ) else 0) := by
    ext i j
    rw [Matrix.circulant_apply, Matrix.one_apply]
    by_cases h : i = j
    · subst h; simp
    · have hsub : i - j ≠ 0 := sub_ne_zero.mpr h
      simp [h, hsub]
  have hmv : ∀ (v : ZMod t → ℝ) (i : ZMod t),
      (Matrix.circulant v *ᵥ v) i = ∑ j : ZMod t, v (i - j) * v j := by
    intro v i
    simp only [Matrix.mulVec, dotProduct, Matrix.circulant_apply]
  have hsum : A * A + B * B + C * C + D * D =
      ((4 * Fintype.card (ZMod t) : ℕ) : ℝ) • (1 : Matrix (ZMod t) (ZMod t) ℝ) := by
    rw [hAdef, hBdef, hCdef, hDdef, Matrix.circulant_mul, Matrix.circulant_mul,
      Matrix.circulant_mul, Matrix.circulant_mul, ← Matrix.circulant_add, ← Matrix.circulant_add,
      ← Matrix.circulant_add, hone, ← Matrix.circulant_smul]
    apply Matrix.circulant_inj.mpr
    funext i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hmv]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib, hauto i,
      hcardZ]
    by_cases h : i = 0
    · simp only [h, if_pos rfl, mul_one]
      push_cast
      ring
    · simp [h]
  obtain ⟨W, hWpm, hWorth⟩ :=
    Williamson_array A B C D hApm hBpm hCpm hDpm hAs hBs hCs hDs hAB hAC hAD hBC hBD hCD hsum
  have hcard4 : Fintype.card ((ZMod t ⊕ ZMod t) ⊕ (ZMod t ⊕ ZMod t)) = 4 * t := by
    simp only [Fintype.card_sum, hcardZ]; ring
  set e : Fin (4 * t) ≃ (ZMod t ⊕ ZMod t) ⊕ (ZMod t ⊕ ZMod t) :=
    (finCongr hcard4.symm).trans (Fintype.equivFin _).symm
  obtain ⟨hMpm, hMorth⟩ :=
    transport_hadamard e W ((4 * Fintype.card (ZMod t) : ℕ) : ℝ) hWpm hWorth
  have hcast : ((4 * Fintype.card (ZMod t) : ℕ) : ℝ) = ((4 * t : ℕ) : ℝ) := by rw [hcardZ]
  rw [hcast] at hMorth
  exact ⟨W.submatrix e e, hMpm, hMorth⟩
