-- Prove2me | solution 1 for SDDiP.Envelope.g_eq_f_binary
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:44:48.704093+00:00
-- url     : https://prove2.me/submissions/3d983d2e-9092-4377-bb2d-9ef22a262828

import Mathlib
import Definitions.Def_SDDiP_Envelope_ProofLP

set_option autoImplicit false
open SDDiP.Envelope

theorem solution {n : ℕ} (f : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) (hx : x ∈ binaryPoints n) :
    IsGreatest (primalValues f x) (f x) ∧ g f x = f x := by
  have key : IsGreatest (primalValues f x) (f x) := by
    set M : ℝ := ∑ b : Fin n → Bool, |f x - f (binVec b)| with hM
    have hM0 : 0 ≤ M := Finset.sum_nonneg (fun b _ => abs_nonneg _)
    set α : Fin n → ℝ := fun i => M * (2 * x i - 1) with hα
    set β : ℝ := f x - M * ∑ i, x i with hβ
    have hval : ∀ y ∈ binaryPoints n,
        α ⬝ᵥ y + β = f x - M * ∑ i, (x i - y i) ^ 2 := by
      intro y hy
      have hpt : ∀ i, M * (2 * x i - 1) * y i = M * x i - M * (x i - y i) ^ 2 := by
        intro i
        rcases hx i with h | h <;> rcases hy i with h' | h' <;> simp [h, h'] <;> ring
      have e1 : α ⬝ᵥ y + β = f x + (∑ i, M * (2 * x i - 1) * y i - M * ∑ i, x i) := by
        simp only [hα, hβ, dotProduct]; ring
      rw [e1, Finset.sum_congr rfl (fun i _ => hpt i), Finset.sum_sub_distrib]
      simp only [← Finset.mul_sum]
      ring
    have hmem : (α, β) ∈ PiPoly f := by
      intro y hy
      show α ⬝ᵥ y + β ≤ f y
      rw [hval y hy]
      by_cases hxy : y = x
      · subst hxy
        simp
      · obtain ⟨i, hi⟩ : ∃ i, y i ≠ x i := by
          by_contra hcon
          push Not at hcon
          exact hxy (funext hcon)
        have hsq : (x i - y i) ^ 2 = 1 := by
          rcases hx i with h | h <;> rcases hy i with h' | h' <;> simp_all
        have hD : 1 ≤ ∑ j, (x j - y j) ^ 2 := by
          calc (1 : ℝ) = (x i - y i) ^ 2 := hsq.symm
            _ ≤ ∑ j, (x j - y j) ^ 2 :=
              Finset.single_le_sum (f := fun j => (x j - y j) ^ 2) (fun j _ => sq_nonneg _)
                (Finset.mem_univ i)
        have hbin : binVec (fun j => decide (y j = 1)) = y := by
          funext j
          rcases hy j with h | h <;> simp [binVec, h]
        have hle : |f x - f y| ≤ M := by
          have := Finset.single_le_sum (f := fun b : Fin n → Bool => |f x - f (binVec b)|)
            (fun b _ => abs_nonneg _) (Finset.mem_univ (fun j => decide (y j = 1)))
          simpa [hbin] using this
        have h1 : f x - f y ≤ M := (le_abs_self _).trans hle
        nlinarith
    refine ⟨⟨(α, β), hmem, ?_⟩, ?_⟩
    · show f x = α ⬝ᵥ x + β
      rw [hval x hx]
      simp
    · rintro v ⟨p, hp, rfl⟩
      exact hp x hx
  exact ⟨key, key.csSup_eq⟩
