-- Prove2me | solution 1 for Research.not_literalClaimAtOne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T18:08:21.388796+00:00
-- url     : https://prove2.me/submissions/29819ab3-169f-4776-bfb7-da4c18557dac

module
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Prod.Lex
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.IntervalCases
public import Definitions.Def_Research_Basic

set_option autoImplicit true
@[expose] public section
public section
open Research
namespace Research
theorem _root_.solution : ¬ LiteralClaimAtOne := by
  rintro ⟨N, hN⟩
  let n := N + 8
  let x : Fin n → ℝ × ℝ := fun i => ((i.val : ℝ), 0)
  have hn : N ≤ n := by
    dsimp [n]
    omega
  have hx : OneSeparated x := by
    intro i j hij
    simp only [sqDist, x, sub_zero]
    have hv : i.val + 1 ≤ j.val ∨ j.val + 1 ≤ i.val := by omega
    rcases hv with hv | hv
    · have hr : (i.val : ℝ) + 1 ≤ (j.val : ℝ) := by exact_mod_cast hv
      nlinarith [sq_nonneg ((i.val : ℝ) - (j.val : ℝ))]
    · have hr : (j.val : ℝ) + 1 ≤ (i.val : ℝ) := by exact_mod_cast hv
      nlinarith [sq_nonneg ((i.val : ℝ) - (j.val : ℝ))]
  have upper := hN n hn x hx
  let i0 : Fin n := ⟨0, by dsimp [n]; omega⟩
  let i1 : Fin n := ⟨1, by dsimp [n]; omega⟩
  let i2 : Fin n := ⟨2, by dsimp [n]; omega⟩
  let i3 : Fin n := ⟨3, by dsimp [n]; omega⟩
  let i4 : Fin n := ⟨4, by dsimp [n]; omega⟩
  let i5 : Fin n := ⟨5, by dsimp [n]; omega⟩
  let i6 : Fin n := ⟨6, by dsimp [n]; omega⟩
  let i7 : Fin n := ⟨7, by dsimp [n]; omega⟩
  let witnesses : Finset (Fin n × Fin n) :=
    {(i0, i1), (i1, i2), (i2, i3), (i3, i4),
      (i4, i5), (i5, i6), (i6, i7)}
  have hwcard : witnesses.card = 7 := by
    simp [witnesses, i0, i1, i2, i3, i4, i5, i6, i7]
  have adjacent_mem (a b : Fin n) (hab : b.val = a.val + 1) :
      (a, b) ∈ shortPairsAtOne x := by
    rw [shortPairsAtOne, Finset.mem_filter]
    constructor
    · simp
    · constructor
      · change a.val < b.val
        rw [hab]
        omega
      · simp [x, sqDist, hab]
  have hwsub : witnesses ⊆ shortPairsAtOne x := by
    intro p hp
    simp only [witnesses, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact adjacent_mem i0 i1 (by rfl)
    · exact adjacent_mem i1 i2 (by rfl)
    · exact adjacent_mem i2 i3 (by rfl)
    · exact adjacent_mem i3 i4 (by rfl)
    · exact adjacent_mem i4 i5 (by rfl)
    · exact adjacent_mem i5 i6 (by rfl)
    · exact adjacent_mem i6 i7 (by rfl)
  have lower : 7 ≤ (shortPairsAtOne x).card := by
    rw [← hwcard]
    exact Finset.card_le_card hwsub
  omega
end Research
