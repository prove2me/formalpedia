-- Prove2me | solution 1 for PinningSync.Tree.lemma_2_13
-- status  : ACCEPTED   (prove)
-- author  : @waitingintime
-- created : 2026-10-10T18:10:41.978551+00:00
-- url     : https://prove2.me/submissions/dcd74fd2-0816-40b5-b6f3-e5a63ea2a680

import Mathlib
open Matrix
open scoped Matrix
set_option autoImplicit false
set_option maxHeartbeats 0
noncomputable section

private lemma strict_schur {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq ι] [DecidableEq κ]
    (Q : Matrix ι ι ℝ) (S : Matrix ι κ ℝ) (R : Matrix κ κ ℝ)
    (hQ : Q.IsHermitian) (hR : R.IsHermitian) :
    (fromBlocks Q S Sᵀ R).PosDef ↔ Q.PosDef ∧ (R - Sᵀ * Q⁻¹ * S).PosDef := by
  constructor
  · intro h
    have hq : Q.PosDef := by
      exact h.submatrix Sum.inl_injective
    letI := hq.isUnit.invertible
    refine ⟨hq, PosDef.of_dotProduct_mulVec_pos ?_ ?_⟩
    · simpa only [conjTranspose_eq_transpose_of_trivial] using
        hR.sub (isHermitian_conjTranspose_mul_mul S hQ.inv)
    · intro y hy
      have hn : (-((Q⁻¹ * S) *ᵥ y) ⊕ᵥ y) ≠ 0 := by
        intro he
        apply hy
        exact congrArg (fun z => z ∘ Sum.inr) he
      have hp := h.dotProduct_mulVec_pos hn
      rw [dotProduct_mulVec] at hp
      rw [← conjTranspose_eq_transpose_of_trivial S,
        schur_complement_eq₁₁ S R _ _ hQ] at hp
      simpa only [conjTranspose_eq_transpose_of_trivial, neg_add_cancel,
        star_zero, zero_vecMul, zero_dotProduct, zero_add, ← dotProduct_mulVec] using hp
  · rintro ⟨hq, hc⟩
    letI := hq.isUnit.invertible
    apply PosDef.of_dotProduct_mulVec_pos
    · simp only [isHermitian_fromBlocks_iff, conjTranspose_eq_transpose_of_trivial,
        transpose_transpose]
      exact ⟨hQ, trivial, trivial, hR⟩
    · intro v hv
      rw [dotProduct_mulVec, ← Sum.elim_comp_inl_inr v,
        ← conjTranspose_eq_transpose_of_trivial S,
        schur_complement_eq₁₁ S R _ _ hQ, ← dotProduct_mulVec, ← dotProduct_mulVec]
      by_cases hy : v ∘ Sum.inr = 0
      · have hx : v ∘ Sum.inl ≠ 0 := by
          intro hx
          apply hv
          ext i
          cases i with
          | inl i => exact congrFun hx i
          | inr i => exact congrFun hy i
        simpa [hy] using hq.dotProduct_mulVec_pos hx
      · exact add_pos_of_nonneg_of_pos (hq.posSemidef.dotProduct_mulVec_nonneg _)
          (hc.dotProduct_mulVec_pos hy)

theorem solution {p q : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ)
    (S : Matrix (Fin p) (Fin q) ℝ) (R : Matrix (Fin q) (Fin q) ℝ)
    (hQ : Qᵀ = Q) (hR : Rᵀ = R) :
    ((Matrix.fromBlocks Q S Sᵀ R).PosDef ↔ (Q.PosDef ∧ (R - Sᵀ * Q⁻¹ * S).PosDef)) ∧
      ((Matrix.fromBlocks Q S Sᵀ R).PosDef ↔ (R.PosDef ∧ (Q - S * R⁻¹ * Sᵀ).PosDef)) := by
  have hq : Q.IsHermitian := by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hQ
  have hr : R.IsHermitian := by simpa only [IsHermitian, conjTranspose_eq_transpose_of_trivial] using hR
  refine ⟨strict_schur Q S R hq hr, ?_⟩
  have hs := strict_schur R Sᵀ Q hr hq
  have he : (fromBlocks Q S Sᵀ R).PosDef ↔ (fromBlocks R Sᵀ S Q).PosDef := by
    constructor <;> intro h
    · simpa only [Equiv.sumComm_apply, fromBlocks_submatrix_sum_swap_sum_swap,
        transpose_transpose] using h.submatrix (Equiv.sumComm (Fin q) (Fin p)).injective
    · simpa only [Equiv.sumComm_apply, fromBlocks_submatrix_sum_swap_sum_swap,
        transpose_transpose] using h.submatrix (Equiv.sumComm (Fin p) (Fin q)).injective
  simpa only [transpose_transpose] using he.trans hs
