-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Extend50.P36.hermitian_marginals_extend
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:09:51.252606+00:00
-- url     : https://prove2.me/submissions/e169b9c1-a4a3-447a-9269-a0e6da31ee5e

import Definitions.Def_QAlgorithms_Papers_Independent_Extend50_P36
noncomputable section

open scoped Matrix ComplexConjugate Matrix.Norms.Elementwise

open MeasureTheory

namespace QAlgorithms.Papers.Independent.Extend50.P36

attribute [local instance] Classical.propDecidable Classical.decEq

-- Exact accepted matrix alias; tensor reductions below compose frozen superoperators.

open QAlgorithms.Papers.Independent.Information100.P21 (Op)

end QAlgorithms.Papers.Independent.Extend50.P36

open QAlgorithms QAlgorithms.Papers.Independent.Extend50.P36
open QAlgorithms.Papers.Independent.Information100.P21 (Op)
attribute [local instance] Classical.propDecidable Classical.decEq

theorem solution {I J K : Type*}
    [Fintype I] [Fintype J] [Fintype K] [Nonempty I] [Nonempty J] [Nonempty K]
    (A : Op (I × J)) (B : Op (I × K))
    (hA : A.IsHermitian) (hB : B.IsHermitian) (htA : A.trace = 1) (htB : B.trace = 1)
    (hconsistent : traceRight A = traceRight B) :
    ∃ X : Op (I × J × K), X.IsHermitian ∧ X.trace = 1 ∧ (idTensorSuperop traceRight) X = A ∧ (idTensorSuperop traceLeft) X = B := by
  set C := traceRight A with hC
  have hJ : (Fintype.card J : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hK : (Fintype.card K : ℂ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨Matrix.of fun p q => A (p.1, p.2.1) (q.1, q.2.1) * (if p.2.2 = q.2.2 then (Fintype.card K : ℂ)⁻¹ else 0)
      + (if p.2.1 = q.2.1 then (Fintype.card J : ℂ)⁻¹ else 0) * B (p.1, p.2.2) (q.1, q.2.2)
      - C p.1 q.1 * (if p.2.1 = q.2.1 then (Fintype.card J : ℂ)⁻¹ else 0)
          * (if p.2.2 = q.2.2 then (Fintype.card K : ℂ)⁻¹ else 0), ?_, ?_, ?_, ?_⟩
  · ext p q
    have h1 := hA.apply (p.1, p.2.1) (q.1, q.2.1)
    have h2 := hB.apply (p.1, p.2.2) (q.1, q.2.2)
    have h3 : star (C q.1 p.1) = C p.1 q.1 := by
      simp only [hC, traceRight, Matrix.of_apply, star_sum]
      exact Finset.sum_congr rfl fun h _ => hA.apply (p.1, h) (q.1, h)
    simp only [Matrix.conjTranspose_apply, Matrix.of_apply, star_sub, star_add, star_mul']
    rw [h1, h2, h3]
    by_cases hj : p.2.1 = q.2.1 <;> by_cases hk : p.2.2 = q.2.2 <;>
      simp [hj, hk, eq_comm]
  · have tA : ∑ i, ∑ j, A (i, j) (i, j) = 1 := by
      rw [← htA, Matrix.trace, Fintype.sum_prod_type]; rfl
    have tB : ∑ i, ∑ k, B (i, k) (i, k) = 1 := by
      rw [← htB, Matrix.trace, Fintype.sum_prod_type]; rfl
    have tC : ∑ i, C i i = 1 := by
      simp only [hC, traceRight, Matrix.of_apply]; exact tA
    simp only [Matrix.trace, Matrix.diag, Matrix.of_apply, Fintype.sum_prod_type, if_true, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
    rw [tA, tB, tC, Fintype.card_prod]
    push_cast
    field_simp
    ring
  · ext p q
    simp only [idTensorSuperop, traceRight, Matrix.of_apply, Finset.sum_add_distrib,
      Finset.sum_sub_distrib, if_true]
    have e1 : ∑ x : K, (if p.2 = q.2 then (Fintype.card J : ℂ)⁻¹ else 0) * B (p.1, x) (q.1, x)
        = (if p.2 = q.2 then (Fintype.card J : ℂ)⁻¹ else 0) * C p.1 q.1 := by
      rw [← Finset.mul_sum, hconsistent]; rfl
    rw [e1]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Prod.mk.eta]
    split_ifs <;> (try simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]) <;> field_simp <;> ring
  · ext p q
    simp only [idTensorSuperop, traceLeft, Matrix.of_apply, Finset.sum_add_distrib,
      Finset.sum_sub_distrib]
    have e1 : ∑ x : J, A (p.1, x) (q.1, x) * (if p.2 = q.2 then (Fintype.card K : ℂ)⁻¹ else 0)
        = C p.1 q.1 * (if p.2 = q.2 then (Fintype.card K : ℂ)⁻¹ else 0) := by
      rw [← Finset.sum_mul]; rfl
    rw [e1]
    simp only [if_true, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Prod.mk.eta]
    split_ifs <;> (try simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]) <;> field_simp <;> ring
