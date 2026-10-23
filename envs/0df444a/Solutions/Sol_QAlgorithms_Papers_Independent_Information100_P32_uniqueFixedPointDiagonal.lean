-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Information100.P32.uniqueFixedPointDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-22T08:21:49.47402+00:00
-- url     : https://prove2.me/submissions/07c9462d-8926-44f2-9375-3c7c973b965d

import Definitions.Def_QAlgorithms_Papers_Independent_Information100_P32

noncomputable section

open scoped Matrix ComplexConjugate Topology ComplexOrder

open Filter MeasureTheory

namespace QAlgorithms.Papers.Independent.Information100.P32

theorem X7u_diag_add {I : Type*} [DecidableEq I] (x y : Op I) :
    diagonal (x + y) = diagonal x + diagonal y := by
  ext i j; by_cases h : i = j <;> simp [diagonal, h]

theorem X7u_diag_sub {I : Type*} [DecidableEq I] (x y : Op I) :
    diagonal (x - y) = diagonal x - diagonal y := by
  ext i j; by_cases h : i = j <;> simp [diagonal, h]

theorem X7u_diag_idem {I : Type*} [DecidableEq I] (x : Op I) :
    diagonal (diagonal x) = diagonal x := by
  ext i j; by_cases h : i = j <;> simp [diagonal, h]

theorem X7u_diag_eq {I : Type*} [DecidableEq I] (x : Op I) :
    diagonal x = Matrix.diagonal (fun i => x i i) := by
  ext i j
  by_cases h : i = j
  · subst h; simp [diagonal]
  · simp [diagonal, h, Matrix.diagonal_apply_ne _ h]

/-- Kraus operators |0><phi0|, |1><phi1| with phi0=(3/5,4/5), phi1=(4/5,-3/5). -/
def X7u_E : Fin 2 → Op Bool := ![
  Matrix.of fun i j => if i then 0 else (if j then (4/5 : ℂ) else 3/5),
  Matrix.of fun i j => if i then (if j then (-3/5 : ℂ) else 4/5) else 0]

def X7u_g : Op Bool → Op Bool := QAlgorithms.krausApply X7u_E

def X7u_s : Op Bool := fun i j => if i = j then (1/2 : ℂ) else 0

theorem X7u_g_apply (x : Op Bool) (i j : Bool) :
    X7u_g x i j =
      if i = j then
        (if i then (16/25 * x false false - 12/25 * x false true - 12/25 * x true false
            + 9/25 * x true true)
          else (9/25 * x false false + 12/25 * x false true + 12/25 * x true false
            + 16/25 * x true true))
      else 0 := by
  cases i <;> cases j <;>
    simp [X7u_g, QAlgorithms.krausApply, X7u_E, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.conjTranspose_apply, map_ofNat] <;> ring

end QAlgorithms.Papers.Independent.Information100.P32

end

noncomputable section

open scoped Matrix ComplexConjugate Topology ComplexOrder

open Filter MeasureTheory

open QAlgorithms QAlgorithms.Papers.Independent.Information100.P32 in
theorem solution {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (f : Op I → Op I) (hf : IsChannel f) (hd : Decoupled f)
    (r : Op I) (hr : IsDensityMatrix r) (hfix : f r = r)
    (hunique : ∀ x, IsDensityMatrix x → f x = x → x = r) :
    diagonal r = r ∧
    (∃ (g : Op Bool → Op Bool) (s : Op Bool), IsChannel g ∧ IsDensityMatrix s ∧
      g s = s ∧ diagonal s = s ∧
      (∀ x, IsDensityMatrix x → g x = x → x = s) ∧ ¬Decoupled g) := by
  constructor
  · -- commuting with dephasing
    obtain ⟨n, E, -, hE⟩ := hf
    have hadd : ∀ x y, f (x + y) = f x + f y := by
      intro x y
      simp only [hE, QAlgorithms.krausApply, Matrix.mul_add, Matrix.add_mul,
        Finset.sum_add_distrib]
    have hcomm : diagonal (f r) = f (diagonal r) := by
      obtain ⟨h1, h2⟩ := hd
      have hx : r = diagonal r + (r - diagonal r) := by abel
      have e1 := h1 (diagonal r) (X7u_diag_idem r)
      have e2 := h2 (r - diagonal r) (by rw [X7u_diag_sub, X7u_diag_idem, sub_self])
      conv_lhs => rw [hx, hadd, X7u_diag_add, e1, e2, add_zero]
    apply hunique
    · refine ⟨?_, ?_⟩
      · rw [X7u_diag_eq, Matrix.posSemidef_diagonal_iff]
        intro i; exact hr.1.diag_nonneg
      · rw [X7u_diag_eq, Matrix.trace_diagonal]; exact hr.2
    · rw [← hcomm, hfix]
  · refine ⟨X7u_g, X7u_s, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨2, X7u_E, ?_, fun _ => rfl⟩
      unfold QAlgorithms.IsKrausFamily
      ext i j
      cases i <;> cases j <;>
        simp [X7u_E, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
          Matrix.one_apply, map_ofNat] <;> norm_num
    · refine ⟨?_, ?_⟩
      · have : X7u_s = Matrix.diagonal (fun _ => (1/2 : ℂ)) := by
          ext i j; by_cases h : i = j
          · subst h; simp [X7u_s]
          · simp [X7u_s, h]
        rw [this, Matrix.posSemidef_diagonal_iff]
        intro i; exact div_nonneg zero_le_one zero_le_two
      · simp [X7u_s, Matrix.trace]
    · ext i j
      rw [X7u_g_apply]
      cases i <;> cases j <;> simp [X7u_s] <;> norm_num
    · ext i j
      cases i <;> cases j <;> simp [X7u_s, diagonal]
    · intro x hx hgx
      have h01 : x false true = 0 := by
        rw [← hgx, X7u_g_apply]; simp
      have h10 : x true false = 0 := by
        rw [← hgx, X7u_g_apply]; simp
      have hff : x false false = 9/25 * x false false + 12/25 * x false true +
          12/25 * x true false + 16/25 * x true true := by
        conv_lhs => rw [← hgx]
        rw [X7u_g_apply]; simp
      have htr : x false false + x true true = 1 := by
        have := hx.2
        simp [Matrix.trace] at this
        rw [add_comm]; exact this
      rw [h01, h10] at hff
      have h1 : x false false = 1/2 := by linear_combination (25/32 : ℂ) * hff + (1/2 : ℂ) * htr
      have h2 : x true true = 1/2 := by linear_combination htr - h1
      ext i j
      cases i <;> cases j <;> simp [X7u_s, h01, h10, h1, h2]
    · rintro ⟨-, h2⟩
      let x : Op Bool := fun i j => if i = j then 0 else 1
      have hx : diagonal x = 0 := by
        ext i j; cases i <;> cases j <;> simp [x, diagonal]
      have := congrFun (congrFun (h2 x hx) false) false
      simp only [diagonal, if_true] at this
      rw [X7u_g_apply] at this
      simp [x] at this

end
