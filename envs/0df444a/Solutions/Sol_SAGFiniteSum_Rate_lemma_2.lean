-- Prove2me | solution 1 for SAGFiniteSum.Rate.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T12:35:08.171446+00:00
-- url     : https://prove2.me/submissions/11a32a5b-7906-4f09-9239-3efef00ba285

import Mathlib
import Definitions.Def_SAGFiniteSum_Rate_Model

open scoped RealInnerProductSpace

theorem solution {p n : ℕ} (hn : 0 < n) (α β : ℝ) (hα : α ≠ 0) (hβ : β ≠ 0) :
    let avgOp : (Fin n → EuclideanSpace ℝ (Fin p)) → (Fin n → EuclideanSpace ℝ (Fin p)) :=
      fun u _ => (1 / (n : ℝ)) • ∑ j, u j
    let M : (Fin n → EuclideanSpace ℝ (Fin p)) → (Fin n → EuclideanSpace ℝ (Fin p)) :=
      fun u => α • (u - avgOp u) + β • avgOp u
    let N : (Fin n → EuclideanSpace ℝ (Fin p)) → (Fin n → EuclideanSpace ℝ (Fin p)) :=
      fun u => α⁻¹ • (u - avgOp u) + β⁻¹ • avgOp u
    ∀ u, M (N u) = u ∧ N (M u) = u := by
  intro avgOp M N u
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnS : ∀ S : EuclideanSpace ℝ (Fin p), (n : ℝ) • ((1 / (n : ℝ)) • S) = S := by
    intro S; rw [smul_smul, mul_one_div_cancel hnR, one_smul]
  -- generic operator
  have hsum : ∀ (c d : ℝ) (v : Fin n → EuclideanSpace ℝ (Fin p)),
      ∑ j, (c • (v - avgOp v) + d • avgOp v) j = d • ∑ j, v j := by
    intro c d v
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply, avgOp]
    rw [Finset.sum_add_distrib, ← Finset.smul_sum, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ,
      ← Nat.cast_smul_eq_nsmul ℝ, hnS, sub_self, smul_zero, zero_add, smul_comm, hnS]
  have hgen : ∀ (a b c d : ℝ), a * c = 1 → b * d = 1 →
      ∀ v : Fin n → EuclideanSpace ℝ (Fin p),
      a • ((c • (v - avgOp v) + d • avgOp v) - avgOp (c • (v - avgOp v) + d • avgOp v)) +
        b • avgOp (c • (v - avgOp v) + d • avgOp v) = v := by
    intro a b c d hac hbd v
    funext i
    have hA : avgOp (c • (v - avgOp v) + d • avgOp v) i = (1 / (n : ℝ)) • (d • ∑ j, v j) := by
      show (1 / (n : ℝ)) • ∑ j, (c • (v - avgOp v) + d • avgOp v) j = _
      rw [hsum]
    simp only [Pi.add_apply, Pi.smul_apply, Pi.sub_apply]
    rw [hA]
    have hAv : avgOp v i = (1 / (n : ℝ)) • ∑ j, v j := rfl
    rw [hAv]
    have : a • (c • (v i - (1 / (n : ℝ)) • ∑ j, v j) + d • (1 / (n : ℝ)) • ∑ j, v j -
        (1 / (n : ℝ)) • d • ∑ j, v j) + b • (1 / (n : ℝ)) • d • ∑ j, v j =
        (a * c) • (v i - (1 / (n : ℝ)) • ∑ j, v j) + (b * d) • ((1 / (n : ℝ)) • ∑ j, v j) := by
      module
    rw [this, hac, hbd, one_smul, one_smul, sub_add_cancel]
  constructor
  · exact hgen α β α⁻¹ β⁻¹ (mul_inv_cancel₀ hα) (mul_inv_cancel₀ hβ) u
  · exact hgen α⁻¹ β⁻¹ α β (inv_mul_cancel₀ hα) (inv_mul_cancel₀ hβ) u
