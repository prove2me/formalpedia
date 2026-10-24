-- Prove2me | solution 1 for RLInference.QValueCLT.I_sub_gamma_PtildePrime_invertible
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-10-24T03:13:02.483881+00:00
-- url     : https://prove2.me/submissions/12c902cf-027a-404d-8831-362ffab5cf1a

import Definitions.Def_RLInference_QValueCLT_Setting
import Mathlib.LinearAlgebra.Matrix.Gershgorin
import Mathlib.Tactic.Linarith
import Mathlib.Analysis.CStarAlgebra.CStarMatrix

open Finset Matrix RLInference.QValueCLT

namespace D24StochasticInverse

theorem isUnit_one_sub_stochastic {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : Matrix ι ι ℝ) (hM : ∀ i j, 0 ≤ M i j) (hrow : ∀ i, ∑ j, M i j = 1)
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1) : IsUnit (1 - γ • M) := by
  apply (Matrix.isUnit_iff_isUnit_det _).2
  apply isUnit_iff_ne_zero.2
  apply det_ne_zero_of_sum_row_lt_diag
  intro i
  have hii : M i i ≤ 1 := by
    calc
      M i i ≤ ∑ j, M i j := single_le_sum (fun j _ => hM i j) (mem_univ i)
      _ = 1 := hrow i
  have hd : 0 ≤ 1 - γ * M i i := by
    have hmul : γ * M i i ≤ γ := by simpa using mul_le_mul_of_nonneg_left hii hγ0
    linarith
  calc
    ∑ j ∈ univ.erase i, ‖(1 - γ • M) i j‖ =
        ∑ j ∈ univ.erase i, γ * M i j := by
      apply sum_congr rfl
      intro j hj
      have hij : i ≠ j := Ne.symm (mem_erase.1 hj).1
      simp [Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, hij,
        Real.norm_eq_abs, abs_of_nonneg hγ0, abs_of_nonneg (hM i j)]
    _ = γ * (1 - M i i) := by
      rw [← mul_sum, sum_erase_eq_sub (mem_univ i), hrow i]
    _ < 1 - γ * M i i := by linarith
    _ = ‖(1 - γ • M) i i‖ := by
      simp [Matrix.sub_apply, Matrix.smul_apply, Real.norm_eq_abs, abs_of_nonneg hd]

end D24StochasticInverse

theorem solution {S A : Type} [Fintype S] [DecidableEq S] [Nonempty S]
    [Fintype A] [DecidableEq A] [Nonempty A]
    (γ : ℝ) (hγ0 : 0 ≤ γ) (hγ1 : γ < 1)
    (P' : S × A → S → ℝ) (hP'_nonneg : ∀ x k, 0 ≤ P' x k)
    (hP'_sum : ∀ x, ∑ k, P' x k = 1)
    (Q' : S × A → ℝ)
    (hQ' : ∀ k : S, ∃ a : A, ∀ a' : A, a' ≠ a → Q' (k, a') < Q' (k, a)) :
    IsUnit (1 - γ • PtildePrime P' Q') := by
  classical
  choose a ha using hQ'
  have hmax : ∀ k, (⨆ u, Q' (k, u)) = Q' (k, a k) := by
    intro k
    apply le_antisymm
    · apply ciSup_le
      intro u
      by_cases hu : u = a k
      · exact le_of_eq (congrArg (fun u => Q' (k, u)) hu)
      · exact (ha k u hu).le
    · exact le_ciSup (Set.finite_range (fun u : A => Q' (k, u))).bddAbove (a k)
  have harg : ∀ k l, (Q' (k, l) = ⨆ u, Q' (k, u)) ↔ l = a k := by
    intro k l
    rw [hmax k]
    constructor
    · intro hl
      by_contra hne
      exact (ne_of_lt (ha k l hne)) hl
    · intro hl
      rw [hl]
  have hrepr : PtildePrime P' Q' = PtildeStar P' a := by
    ext x y
    simp only [PtildePrime, PtildeStar, harg]
  rw [hrepr]
  apply D24StochasticInverse.isUnit_one_sub_stochastic _ _ _ γ hγ0 hγ1
  · intro x y
    simp only [PtildeStar]
    split_ifs <;> simp [hP'_nonneg]
  · intro x
    simp only [PtildeStar]
    rw [Fintype.sum_prod_type]
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
    exact hP'_sum x

#print axioms solution
