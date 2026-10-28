-- Prove2me | solution 1 for SPHardness.IntFeas.lemma_4
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T07:13:14.129723+00:00
-- url     : https://prove2.me/submissions/78208d0b-d4ec-4977-8847-b4b8b08892e7

import Mathlib
import Definitions.Def_SPHardness_IntFeas_Model

open MeasureTheory

open SPHardness.IntFeas in
theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℤ) (b : Fin m → ℤ)
    (hinst : IsIFPInstance A b)
    (ε' : ℝ) (hε'0 : 0 ≤ ε') (hε'half : ε' < 1 / 2)
    (hε'row : ∀ i, ε' * ∑ j, |(A i j : ℝ)| < 1) :
    IFPAnswer A b ↔
      ∃ y : Fin n → ℝ, (∀ j, (0 ≤ y j ∧ y j ≤ ε') ∨ (1 - ε' ≤ y j ∧ y j ≤ 1)) ∧
        InPolytope A b y := by
  constructor
  · rintro ⟨y, hy, hp⟩
    refine ⟨y, fun j => ?_, hp⟩
    rcases hy j with h | h
    · left; rw [h]; exact ⟨le_refl _, hε'0⟩
    · right; rw [h]; constructor <;> linarith
  · rintro ⟨y, hy, hp⟩
    let z : Fin n → ℤ := fun j => if y j ≤ ε' then 0 else 1
    have hz : ∀ j, |(z j : ℝ) - y j| ≤ ε' := by
      intro j
      by_cases h : y j ≤ ε'
      · have hzj : z j = 0 := if_pos h
        rw [hzj]
        rcases hy j with h' | h'
        · rw [abs_le]; constructor <;> push_cast <;> linarith
        · exfalso; linarith
      · have hzj : z j = 1 := if_neg h
        rw [hzj]
        rcases hy j with h' | h'
        · exfalso; linarith
        · rw [abs_le]; constructor <;> push_cast <;> linarith
    refine ⟨fun j => (z j : ℝ), fun j => ?_, fun i => ?_⟩
    · by_cases h : y j ≤ ε'
      · left; show ((if y j ≤ ε' then (0:ℤ) else 1 : ℤ) : ℝ) = 0; rw [if_pos h]; simp
      · right; show ((if y j ≤ ε' then (0:ℤ) else 1 : ℤ) : ℝ) = 1; rw [if_neg h]; simp
    · have hdiff : ∑ j, (A i j : ℝ) * (z j : ℝ) - ∑ j, (A i j : ℝ) * y j ≤
          ε' * ∑ j, |(A i j : ℝ)| := by
        rw [← Finset.sum_sub_distrib, Finset.mul_sum]
        apply Finset.sum_le_sum
        intro j _
        rw [← mul_sub]
        calc (A i j : ℝ) * ((z j : ℝ) - y j) ≤ |(A i j : ℝ) * ((z j : ℝ) - y j)| := le_abs_self _
          _ = |(A i j : ℝ)| * |(z j : ℝ) - y j| := abs_mul _ _
          _ ≤ |(A i j : ℝ)| * ε' := mul_le_mul_of_nonneg_left (hz j) (abs_nonneg _)
          _ = ε' * |(A i j : ℝ)| := mul_comm _ _
      have hlt : ∑ j, (A i j : ℝ) * (z j : ℝ) < (b i : ℝ) + 1 := by
        have := hp i
        have := hε'row i
        linarith
      have hcast : ∑ j, (A i j : ℝ) * (z j : ℝ) = ((∑ j, A i j * z j : ℤ) : ℝ) := by push_cast; rfl
      rw [hcast] at hlt ⊢
      have hlt' : ∑ j, A i j * z j < b i + 1 := by exact_mod_cast hlt
      have : ∑ j, A i j * z j ≤ b i := by omega
      exact_mod_cast this
