-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.decouplingCriterion
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:21:47.264573+00:00
-- url     : https://prove2.me/submissions/f4bbf8d3-c24d-48c9-9e0b-25970711441b

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

theorem X7_diag_add {I : Type*} [DecidableEq I] (x y : Op I) :
    diagonal (x + y) = diagonal x + diagonal y := by
  ext i j; by_cases h : i = j <;> simp [diagonal, h]

theorem X7_diag_sub {I : Type*} [DecidableEq I] (x y : Op I) :
    diagonal (x - y) = diagonal x - diagonal y := by
  ext i j; by_cases h : i = j <;> simp [diagonal, h]

theorem X7_diag_idem {I : Type*} [DecidableEq I] (x : Op I) :
    diagonal (diagonal x) = diagonal x := by
  ext i j; by_cases h : i = j <;> simp [diagonal, h]

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (f : Op I → Op I) (hf : IsChannel f) :
    Decoupled f ↔ ∀ x : Op I, diagonal (f x) = f (diagonal x) := by
  obtain ⟨n, E, -, hE⟩ := hf
  have hadd : ∀ x y, f (x + y) = f x + f y := by
    intro x y
    simp only [hE, QAlgorithms.krausApply, Matrix.mul_add, Matrix.add_mul,
      Finset.sum_add_distrib]
  have hzero : f 0 = 0 := by
    simp [hE, QAlgorithms.krausApply]
  constructor
  · rintro ⟨h1, h2⟩ x
    have hx : x = diagonal x + (x - diagonal x) := by abel
    have e1 := h1 (diagonal x) (X7_diag_idem x)
    have e2 := h2 (x - diagonal x) (by rw [X7_diag_sub, X7_diag_idem, sub_self])
    conv_lhs => rw [hx, hadd, X7_diag_add, e1, e2, add_zero]
  · intro h
    refine ⟨fun x hx => ?_, fun x hx => ?_⟩
    · rw [h, hx]
    · rw [h, hx, hzero]

end
