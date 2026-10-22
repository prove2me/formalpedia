-- Prove2me | solution 1 for ProjReflGrad.Weak.lemma_2_7
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:28:41.760813+00:00
-- url     : https://prove2.me/submissions/20e56cc8-367a-4530-84d9-61b32d20515a

import Mathlib
import Definitions.Def_ProjReflGrad_Weak_Setting

set_option autoImplicit false
open ProjReflGrad.Weak

theorem solution (a b : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n) (hb : ∀ n, 0 ≤ b n)
    (hab : ∀ n, a (n + 1) ≤ a n - b n) :
    Bornology.IsBounded (Set.range a) ∧ Filter.Tendsto b Filter.atTop (nhds 0) := by
  have hmono : ∀ n, a n ≤ a 0 := by
    intro n
    induction n with
    | zero => exact le_refl _
    | succ k ih => have := hab k; have := hb k; linarith
  have hsum : ∀ n, ∑ i ∈ Finset.range n, b i ≤ a 0 - a n := by
    intro n
    induction n with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ]; have := hab k; linarith
  refine ⟨?_, ?_⟩
  · rw [isBounded_iff_forall_norm_le]
    refine ⟨a 0, ?_⟩
    rintro _ ⟨n, rfl⟩
    rw [Real.norm_of_nonneg (ha n)]
    exact hmono n
  · have hs : Summable b := by
      apply summable_of_sum_range_le hb (c := a 0)
      intro n
      have := hsum n
      have := ha n
      linarith
    exact hs.tendsto_atTop_zero
