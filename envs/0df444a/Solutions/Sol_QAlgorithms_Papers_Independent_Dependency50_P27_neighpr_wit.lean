-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Dependency50.P27.neighpr_wit
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:27:01.343771+00:00
-- url     : https://prove2.me/submissions/12050858-c46d-455a-b51c-0729293ea3ae

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Dependency50_P27

set_option autoImplicit false

noncomputable section

open QAlgorithms.Papers.Independent.Dependency50.P27

theorem rootsAux_gt {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (n : ℕ) (p : Polynomial R) (a b : R) :
    ∀ y ∈ rootsAux n p a b, a < y := by
  cases n with
  | zero => intro y hy; simp [rootsAux] at hy
  | succ n =>
    intro y hy
    simp only [rootsAux] at hy
    split_ifs at hy with h
    · simp at hy
    · have := (List.mem_filter.mp hy).2
      simp at this
      exact this.1

theorem neighpr_wit_aux {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (x b : R) (hxb : x < b) (hp : p ≠ 0) :
    x < nextRoot p x b := by
  unfold nextRoot
  rw [if_neg hp]
  cases h : (roots p x b) with
  | nil => simp [max_eq_left hxb.le, hxb]
  | cons y ys =>
    simp only [List.headD_cons]
    apply rootsAux_gt (p.natDegree + 1) p x b
    unfold roots at h
    rw [h]; simp

theorem solution {R : Type*} [Field R] [LinearOrder R] [IsStrictOrderedRing R]
    [PolynomialIVT R] (p : Polynomial R) (x b : R) (hxb : x < b) (hp : p ≠ 0) :
    ∃ y : R, y ∈ neighpr p x b := by
  have h := neighpr_wit_aux p x b hxb hp
  refine ⟨(x + nextRoot p x b) / 2, ?_⟩
  unfold neighpr
  constructor <;> linarith

end
