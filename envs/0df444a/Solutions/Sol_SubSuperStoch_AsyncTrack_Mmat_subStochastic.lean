-- Prove2me | solution 1 for SubSuperStoch.AsyncTrack.Mmat_subStochastic
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-26T10:39:09.670904+00:00
-- url     : https://prove2.me/submissions/7ac7250b-6d47-45b9-ae33-9c3b6cbf9ffc

import Definitions.Def_SubSuperStoch_AsyncTrack_Matrix
import Definitions.Def_SubSuperStoch_AsyncTrack_AsyncModel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

open Matrix Finset SubSuperStoch.AsyncTrack
attribute [local instance] Classical.propDecidable Classical.decEq

set_option autoImplicit false

namespace D26AsyncMatrix

lemma entry {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (τ ψ : ℝ) (s : Fin n → ℕ → ℕ) (k : ℕ) (i j : Fin n) :
    Mmat a b τ ψ s k i j =
      if active s i k then
        (if i = j then 1 - (τ * ψ) * ((∑ z, |a i z|) + |b i|) else 0) +
          (τ * ψ) * |a i j|
      else if i = j then 1 else 0 := by
  classical
  change ((if i = j then 1 else 0) -
      (τ*ψ) * (if i = j then (∑ z, |if active s i k then a i z else 0|) else 0) -
      (τ*ψ) * (if i = j then (if active s i k then |b i| else 0) else 0) +
      (τ*ψ) * |if active s i k then a i j else 0|) = _
  by_cases hij : i = j
  · subst j
    by_cases ha : active s i k <;> simp [ha] <;> ring
  · by_cases ha : active s i k <;> simp [ha,hij]

lemma row {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (τ ψ : ℝ) (s : Fin n → ℕ → ℕ) (k : ℕ) (i : Fin n) :
    rowSum (Mmat a b τ ψ s k) i =
      if active s i k then 1 - (τ * ψ) * |b i| else 1 := by
  classical
  by_cases ha : active s i k
  · simp only [rowSum, entry, if_pos ha, sum_add_distrib, ← mul_sum]
    simp
    ring
  · simp [rowSum, entry, ha]

end D26AsyncMatrix

theorem solution {n : ℕ} (a : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (τ ψ : ℝ) (hτ : 0 < τ) (hψ : 0 < ψ) (s : Fin n → ℕ → ℕ)
    (dM : ℝ) (hdM : IsGreatest {x | ∃ i, x = ∑ j, |a i j| + |b i|} dM)
    (h37 : ψ < 1 / (τ * dM)) :
    ∀ k, IsSubStochastic (Mmat a b τ ψ s k) ∧ (∀ i, 0 < Mmat a b τ ψ s k i i) ∧
      ∀ i, ((active s i k ∧ b i ≠ 0) → rowSum (Mmat a b τ ψ s k) i < 1) ∧
        (¬(active s i k ∧ b i ≠ 0) → rowSum (Mmat a b τ ψ s k) i = 1) := by
  classical
  have hdpos : 0 < dM := by
    by_contra hn
    have hinv : 1 / (τ * dM) ≤ 0 :=
      div_nonpos_of_nonneg_of_nonpos (by norm_num)
        (mul_nonpos_of_nonneg_of_nonpos hτ.le (le_of_not_gt hn))
    linarith
  have hscale : 0 < τ * ψ := mul_pos hτ hψ
  have hbig : τ * ψ * dM < 1 := by
    have := (lt_div_iff₀ (mul_pos hτ hdpos)).mp h37
    nlinarith
  have hrow : ∀ i, 0 < 1 - (τ * ψ) * ((∑ j, |a i j|) + |b i|) := by
    intro i
    have hle := hdM.2 (show (∑ j, |a i j| + |b i|) ∈ {x | ∃ i, x = ∑ j, |a i j| + |b i|} from ⟨i, rfl⟩)
    have hdegree : (∑ j, |a i j|) + |b i| ≤ dM := hle
    have := mul_le_mul_of_nonneg_left hdegree hscale.le
    linarith
  intro k
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j
    rw [D26AsyncMatrix.entry]
    split_ifs with ha hij hij
    · exact add_nonneg (hrow i).le (mul_nonneg hscale.le (abs_nonneg _))
    · exact add_nonneg (le_refl 0) (mul_nonneg hscale.le (abs_nonneg _))
    · norm_num
    · norm_num
  · intro i
    rw [D26AsyncMatrix.row]
    split_ifs <;> nlinarith [mul_nonneg hscale.le (abs_nonneg (b i))]
  · intro i
    rw [D26AsyncMatrix.entry]
    by_cases ha : active s i k
    · simp only [if_pos ha, if_pos rfl]
      exact add_pos_of_pos_of_nonneg (hrow i) (mul_nonneg hscale.le (abs_nonneg _))
    · simp [ha]
  · intro i
    constructor
    · rintro ⟨ha, hb⟩
      rw [D26AsyncMatrix.row, if_pos ha]
      have := mul_pos hscale (abs_pos.mpr hb)
      linarith
    · intro hh
      rw [D26AsyncMatrix.row]
      by_cases ha : active s i k
      · have hb : b i = 0 := by by_contra hb; exact hh ⟨ha, hb⟩
        simp [ha, hb]
      · simp [ha]

#print axioms solution






