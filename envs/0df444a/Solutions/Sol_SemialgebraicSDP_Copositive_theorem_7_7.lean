-- Prove2me | solution 1 for SemialgebraicSDP.Copositive.theorem_7_7
-- status  : ACCEPTED   (prove)
-- author  : @sometik179
-- created : 2026-10-22T05:42:33.69278+00:00
-- url     : https://prove2.me/submissions/7a232ae9-2b0c-458f-b954-bf64079fe0b8

import Mathlib
import Definitions.Def_MurtyKabadi_Reduction_QuadraticProblems
import Definitions.Def_SemialgebraicSDP_Copositive_Forms
import Definitions.Def_SemialgebraicSDP_Copositive_Certificates
open scoped BigOperators
open Matrix MvPolynomial SemialgebraicSDP.Copositive MurtyKabadi.Reduction

open scoped BigOperators
open Matrix MvPolynomial SemialgebraicSDP.Copositive MurtyKabadi.Reduction

namespace CopositiveSDPProof

 theorem triple_cycle {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ) :
    (∑ i, ∑ j, ∑ k, f j k i) = ∑ i, ∑ j, ∑ k, f i j k := by
  exact Finset.sum_comm_cycle.symm

 theorem cyclic_coefficient_nonneg {n : ℕ}
    (Λ : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hd : ∀ i, Λ i i i = 0)
    (hc : ∀ i j, i ≠ j → Λ i j j + Λ j j i + Λ j i j = 0)
    (ht : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      0 ≤ Λ i j k + Λ j k i + Λ k i j) (i j k : Fin n) :
    0 ≤ Λ i j k + Λ j k i + Λ k i j := by
  by_cases hij : i = j
  · subst j
    by_cases hik : i = k
    · subst k
      simp [hd]
    · have h := hc k i (Ne.symm hik)
      linarith
  · by_cases hjk : j = k
    · subst k
      exact le_of_eq (hc i j hij).symm
    · by_cases hik : i = k
      · subst k
        have h := hc j i (Ne.symm hij)
        linarith
      · exact ht i j k hij hjk hik

 theorem cyclic_remainder_nonneg {n : ℕ}
    (Λ : Fin n → Matrix (Fin n) (Fin n) ℝ)
    (hd : ∀ i, Λ i i i = 0)
    (hc : ∀ i j, i ≠ j → Λ i j j + Λ j j i + Λ j i j = 0)
    (ht : ∀ i j k, i ≠ j → j ≠ k → i ≠ k →
      0 ≤ Λ i j k + Λ j k i + Λ k i j)
    (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ ∑ i, ∑ j, ∑ k, Λ i j k * x i * x j * x k := by
  have h1 : (∑ i, ∑ j, ∑ k, Λ j k i * x i * x j * x k) =
      ∑ i, ∑ j, ∑ k, Λ i j k * x i * x j * x k := by
    calc
      _ = ∑ i, ∑ j, ∑ k, Λ j k i * x j * x k * x i := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := triple_cycle (fun i j k => Λ i j k * x i * x j * x k)
  have h2 : (∑ i, ∑ j, ∑ k, Λ k i j * x i * x j * x k) =
      ∑ i, ∑ j, ∑ k, Λ i j k * x i * x j * x k := by
    calc
      _ = ∑ i, ∑ j, ∑ k, Λ k i j * x j * x k * x i := by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := (triple_cycle (fun i j k => Λ j k i * x i * x j * x k)).trans h1
  have hnon : 0 ≤ ∑ i, ∑ j, ∑ k,
      (Λ i j k + Λ j k i + Λ k i j) * x i * x j * x k := by
    apply Finset.sum_nonneg
    intro i _
    apply Finset.sum_nonneg
    intro j _
    apply Finset.sum_nonneg
    intro k _
    exact mul_nonneg (mul_nonneg (mul_nonneg
      (cyclic_coefficient_nonneg Λ hd hc ht i j k) (hx i)) (hx j)) (hx k)
  simp_rw [add_mul, Finset.sum_add_distrib] at hnon
  rw [h1, h2] at hnon
  linarith

 theorem weighted_quadratic_identity {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℝ)
    (Λ : Fin n → Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    (∑ i, x i) * Q M x =
      (∑ i, x i * Q (M - Λ i) x) +
        ∑ i, ∑ j, ∑ k, Λ i j k * x i * x j * x k := by
  simp only [Q, Matrix.mulVec, dotProduct, Matrix.sub_apply]
  simp_rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

end CopositiveSDPProof

open scoped BigOperators
open Matrix MvPolynomial SemialgebraicSDP.Copositive MurtyKabadi.Reduction

namespace CopositiveSDPProof

theorem feasible77_copositive {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : Feasible77 M) : MurtyKabadi.Reduction.Copositive M := by
  obtain ⟨Λ, _, hp, hd, hc, ht⟩ := h
  intro x hx
  have hw : 0 ≤ ∑ i, x i * Q (M - Λ i) x := by
    apply Finset.sum_nonneg
    intro i _
    apply mul_nonneg (hx i)
    simpa only [Q, star_trivial] using (hp i).dotProduct_mulVec_nonneg x
  have hr := cyclic_remainder_nonneg Λ hd hc ht x hx
  have hall : 0 ≤ (∑ i, x i) * Q M x := by
    rw [weighted_quadratic_identity M Λ x]
    exact add_nonneg hw hr
  have hs : 0 ≤ ∑ i, x i := Finset.sum_nonneg (fun i _ => hx i)
  rcases hs.eq_or_lt with hs0 | hspos
  · have hz : x = 0 := by
      funext i
      have hxi : x i ≤ ∑ j, x j := Finset.single_le_sum
        (fun j _ => hx j) (Finset.mem_univ i)
      have : x i = 0 := le_antisymm (hxi.trans_eq hs0.symm) (hx i)
      exact this
    subst x
    simp [Q]
  · exact nonneg_of_mul_nonneg_right hall hspos

end CopositiveSDPProof

open scoped BigOperators
open Matrix MvPolynomial SemialgebraicSDP.Copositive MurtyKabadi.Reduction

namespace CopositiveSDPProof

theorem qform_sum {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (x : Fin n → ℝ) :
    MurtyKabadi.Reduction.Q M x = ∑ i, ∑ j, M i j * x i * x j := by
  classical
  simp only [MurtyKabadi.Reduction.Q, dotProduct, mulVec, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem formP1_eval {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (z : Fin n → ℝ) :
    MvPolynomial.eval z (formP1 M) =
      (∑ i, z i ^ 2) * MurtyKabadi.Reduction.Q M (fun i => z i ^ 2) := by
  classical
  simp only [formP1, map_sum, map_mul, map_pow, eval_C, eval_X]
  rw [qform_sum]
  calc
    (∑ i, ∑ j, ∑ k, M i j * z i ^ 2 * z j ^ 2 * z k ^ 2) =
        ∑ k, ∑ i, ∑ j, M i j * z i ^ 2 * z j ^ 2 * z k ^ 2 :=
      Finset.sum_comm_cycle
    _ = (∑ k, z k ^ 2) * ∑ i, ∑ j, M i j * z i ^ 2 * z j ^ 2 := by
      simp_rw [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem formP1_nonneg_of_copositive {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (h : MurtyKabadi.Reduction.Copositive M) :
    ∀ z : Fin n → ℝ, 0 ≤ MvPolynomial.eval z (formP1 M) := by
  intro z
  rw [formP1_eval]
  exact mul_nonneg (Finset.sum_nonneg fun i _ => sq_nonneg (z i))
    (h _ fun i => sq_nonneg (z i))

end CopositiveSDPProof

open scoped BigOperators
open Matrix MvPolynomial SemialgebraicSDP.Copositive MurtyKabadi.Reduction

namespace CopositiveSDPProof

noncomputable def diagonalCorrection {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (i j : Fin n) : ℝ :=
  if j = i then N j j else N j j + 2 * N i j

noncomputable def certificateFamily {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (i : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  N - Matrix.diagonal (diagonalCorrection N i)

theorem diagonalCorrection_nonneg {n : ℕ} (N : Matrix (Fin n) (Fin n) ℝ)
    (hN : ∀ i j, 0 ≤ N i j) (i : Fin n) : 0 ≤ diagonalCorrection N i := by
  intro j
  unfold diagonalCorrection
  split_ifs
  · exact hN j j
  · exact add_nonneg (hN j j) (mul_nonneg (by norm_num) (hN i j))

theorem cond76_feasible77 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ)
    (hM : M.IsSymm) (h : Cond76 M) : Feasible77 M := by
  classical
  obtain ⟨P, N, hMN, hP, hN⟩ := h
  have hPs : P.IsSymm := Matrix.isHermitian_iff_isSymm.mp hP.isHermitian
  have hNs : N.IsSymm := by
    have hsub : N = M - P := by rw [hMN]; abel
    rw [hsub]
    exact hM.sub hPs
  refine ⟨certificateFamily N, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    exact hNs.sub (Matrix.isSymm_diagonal _)
  · intro i
    have heq : M - certificateFamily N i = P + Matrix.diagonal (diagonalCorrection N i) := by
      rw [hMN]
      unfold certificateFamily
      abel
    rw [heq]
    exact hP.add (Matrix.PosSemidef.diagonal (diagonalCorrection_nonneg N hN i))
  · intro i
    simp [certificateFamily, diagonalCorrection]
  · intro i j hij
    have hji : j ≠ i := Ne.symm hij
    simp only [certificateFamily, Matrix.sub_apply, Matrix.diagonal_apply,
      diagonalCorrection, if_neg hij, if_neg hji, sub_zero, ite_true]
    rw [hNs.apply i j]
    ring
  · intro i j k hij hjk hik
    simp only [certificateFamily, Matrix.sub_apply, Matrix.diagonal_apply,
      if_neg hjk, if_neg (Ne.symm hik), if_neg hij, sub_zero]
    exact add_nonneg (add_nonneg (hN j k) (hN k i)) (hN i j)

end CopositiveSDPProof

namespace SemialgebraicSDP.Copositive

open MvPolynomial

/-- Theorem 7.7 (Parrilo 2003, p. 318). Let `M` be a real symmetric `n × n` matrix. If the
SDPs (7.7) have a feasible solution, then `P₁(z)` is nonnegative, and therefore `M` is
copositive. Furthermore, the test is at least as powerful as condition (7.6): whenever (7.6)
holds, (7.7) is feasible. -/
theorem theorem_7_7 {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (Feasible77 M →
        (∀ z : Fin n → ℝ, 0 ≤ eval z (formP1 M)) ∧ MurtyKabadi.Reduction.Copositive M) ∧
      (Cond76 M → Feasible77 M) := by
  constructor
  · intro h
    have hc := CopositiveSDPProof.feasible77_copositive M h
    exact ⟨CopositiveSDPProof.formP1_nonneg_of_copositive M hc, hc⟩
  · exact CopositiveSDPProof.cond76_feasible77 M hM

end SemialgebraicSDP.Copositive

open SemialgebraicSDP.Copositive MvPolynomial

theorem solution {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (hM : M.IsSymm) :
    (Feasible77 M →
        (∀ z : Fin n → ℝ, 0 ≤ eval z (formP1 M)) ∧ MurtyKabadi.Reduction.Copositive M) ∧
      (Cond76 M → Feasible77 M) := by
  exact SemialgebraicSDP.Copositive.theorem_7_7 M hM
