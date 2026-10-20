-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P11.swap_one_step_delay
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-20T00:50:49.554356+00:00
-- url     : https://prove2.me/submissions/50c78e45-30c6-4536-9596-7b0268f77208

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P11

noncomputable section

open QAlgorithms QAlgorithms.Papers QAlgorithms.Papers.Independent QAlgorithms.Papers.Independent.Dependency50 QAlgorithms.Papers.Independent.Dependency50.P11

open scoped Matrix ComplexConjugate ComplexOrder

open QAlgorithms.Papers.Independent.Information100.P23 (Operator)

lemma g52a_swap_conj {ι : Type*} [Fintype ι] [DecidableEq ι] (M : Matrix (ι × ι) (ι × ι) ℂ)
    (p q : ι × ι) :
    ((swapOp : Matrix (ι × ι) (ι × ι) ℂ) * M * (swapOp : Matrix (ι × ι) (ι × ι) ℂ)ᴴ) p q =
      M (p.2, p.1) (q.2, q.1) := by
  have h1 : ∀ r, ((swapOp : Matrix (ι × ι) (ι × ι) ℂ) * M) p r = M (p.2, p.1) r := by
    intro r
    rw [Matrix.mul_apply, Finset.sum_eq_single (p.2, p.1)]
    · simp [swapOp]
    · intro t _ ht
      have : p ≠ (t.2, t.1) := by
        rintro rfl; exact ht rfl
      simp [swapOp, this]
    · simp
  rw [Matrix.mul_apply, Finset.sum_eq_single (q.2, q.1)]
  · rw [h1]; simp [swapOp]
  · intro t _ ht
    have : q ≠ (t.2, t.1) := by
      rintro rfl; exact ht rfl
    simp [swapOp, this]
  · simp

/-- Section II.A, PDF pp.2–3, (2.4): qubit SWAP outputs the initializer first and
then the preceding input. Includes the exact first-block average, for N>0. -/
theorem solution (D : MemoryDevice 2 2)
    (hSwap : (D.unitary : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) =
      (swapOp : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ)) :
    (∀ input : ℕ → Operator 2, (∀ j, IsDensityMatrix (input j)) →
      outputState D input 0 = D.initial ∧
        ∀ j, outputState D input (j + 1) = input j) ∧
    (∀ rho : Operator 2, IsDensityMatrix rho → ∀ N : ℕ, 0 < N →
      firstBlockMean D rho N = ((N : ℂ)⁻¹) • D.initial +
        (((N - 1 : ℕ) : ℂ) / (N : ℂ)) • rho) := by
  have hjs : ∀ (xi rho : Operator 2), jointStep D xi rho =
      Matrix.of fun p q => xi p.2 q.2 * rho p.1 q.1 := by
    intro xi rho
    ext p q
    unfold jointStep
    rw [hSwap, g52a_swap_conj]
    simp [Matrix.kronecker]
  have hmem : ∀ (input : ℕ → Operator 2) j, memoryState D input (j+1) =
      (memoryState D input j).trace • input j := by
    intro input j
    show traceRight (jointStep D _ _) = _
    rw [hjs]
    ext a b
    simp [traceRight, Matrix.trace, Finset.sum_mul]
    ring
  have hout : ∀ (input : ℕ → Operator 2) j, outputState D input j =
      (input j).trace • memoryState D input j := by
    intro input j
    unfold outputState
    rw [hjs]
    ext a b
    simp [traceLeft, Matrix.trace, Finset.sum_mul, mul_comm]
    ring
  have part1 : ∀ input : ℕ → Operator 2, (∀ j, IsDensityMatrix (input j)) →
      outputState D input 0 = D.initial ∧ ∀ j, outputState D input (j + 1) = input j := by
    intro input hin
    have htr : ∀ j, (memoryState D input j).trace = 1 := by
      intro j
      induction j with
      | zero => exact D.initial_density.2
      | succ j ih => rw [hmem, Matrix.trace_smul, ih, (hin j).2, smul_eq_mul, one_mul]
    refine ⟨?_, fun j => ?_⟩
    · rw [hout, (hin 0).2, one_smul]; try rfl
    · rw [hout, (hin (j+1)).2, one_smul, hmem, htr, one_smul]
  refine ⟨part1, fun rho hrho N hN => ?_⟩
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  obtain ⟨h0, hs⟩ := part1 (fun _ => rho) (fun _ => hrho)
  unfold firstBlockMean
  rw [Finset.sum_range_succ', h0]
  simp only [hs, Finset.sum_const, Finset.card_range, Nat.add_sub_cancel]
  rw [smul_add, add_comm, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
  congr 2
  push_cast
  ring


end

