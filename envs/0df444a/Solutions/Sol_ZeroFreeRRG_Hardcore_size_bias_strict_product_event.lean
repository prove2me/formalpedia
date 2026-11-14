-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.size_bias_strict_product_event
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T07:28:05.873207+00:00
-- url     : https://prove2.me/submissions/83bf5396-0920-442b-b07e-e9068bc126d9

import Mathlib
set_option autoImplicit false
open scoped BigOperators
open MeasureTheory Set

theorem solution (d : ℕ) (hd : 2 ≤ d) (π : Measure (ℝ × ℝ)) [IsProbabilityMeasure π]
    (hs : 0 < π {p | p.1 < p.2}) (hp : 0 < π {p | 0 < p.1}) :
    0 < (Measure.pi fun _ : Fin d => π)
      {xs | (xs ⟨0,by omega⟩).1 < (xs ⟨0,by omega⟩).2 ∧
        (xs ⟨1,by omega⟩).1 < (xs ⟨1,by omega⟩).2 ∧
        ∀ a, a ≠ ⟨0,by omega⟩ → a ≠ ⟨1,by omega⟩ → 0 < (xs a).1} := by
  classical
  let i : Fin d := ⟨0,by omega⟩
  let j : Fin d := ⟨1,by omega⟩
  have hij : i ≠ j := by intro h; have hh := congrArg Fin.val h; simp [i,j] at hh
  let s : Fin d → Set (ℝ × ℝ) := fun a =>
    if a=i ∨ a=j then {p | p.1 < p.2} else {p | 0 < p.1}
  have hsub : univ.pi s ⊆ {xs | (xs i).1 < (xs i).2 ∧ (xs j).1 < (xs j).2 ∧
      ∀ a, a ≠ i → a ≠ j → 0 < (xs a).1} := by
    intro xs hxs
    have hh : ∀ a, xs a ∈ s a := (Set.mem_univ_pi.mp hxs)
    constructor
    · simpa [s] using hh i
    constructor
    · simpa [s] using hh j
    · intro a hai haj
      simpa [s,hai,haj] using hh a
  have hm : 0 < (Measure.pi fun _ : Fin d => π) (univ.pi s) := by
    rw [Measure.pi_pi]
    apply pos_iff_ne_zero.mpr
    apply Finset.prod_ne_zero_iff.mpr
    intro a ha
    dsimp [s]
    split_ifs <;> exact ne_of_gt (by assumption)
  exact lt_of_lt_of_le hm (measure_mono hsub)
