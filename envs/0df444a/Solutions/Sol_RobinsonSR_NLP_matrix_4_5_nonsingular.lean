-- Prove2me | solution 1 for RobinsonSR.NLP.matrix_4_5_nonsingular
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:22:49.351449+00:00
-- url     : https://prove2.me/submissions/f936e91d-4220-41e8-aed9-b51cb51e28df

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix
open Matrix
open RobinsonSR.NLP
set_option autoImplicit false

theorem solution {ιn ιq ιr : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ)
    (hSSOSC : ∀ y : ιn → ℝ, y ≠ 0 → Gp *ᵥ y = 0 → H *ᵥ y = 0 → 0 < y ⬝ᵥ (Q *ᵥ y))
    (hLI : ∀ (b : ιq → ℝ) (c : ιr → ℝ), Hᵀ *ᵥ b + Gpᵀ *ᵥ c = 0 → b = 0 ∧ c = 0) :
    (kktMatrix Q H Gp).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv, he⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  let y : ιn → ℝ := fun i => v (Sum.inl i)
  let b : ιq → ℝ := fun i => v (Sum.inr (Sum.inl i))
  let c : ιr → ℝ := fun i => v (Sum.inr (Sum.inr i))
  have htop : Q *ᵥ y + (Hᵀ *ᵥ b + Gpᵀ *ᵥ c) = 0 := by
    funext i
    have hi := congrFun he (Sum.inl i)
    simpa [kktMatrix, mulVec, dotProduct, Fintype.sum_sum_type, y, b, c,
      Finset.sum_add_distrib] using hi
  have hH : H *ᵥ y = 0 := by
    funext i
    have hi := congrFun he (Sum.inr (Sum.inl i))
    simpa [kktMatrix, mulVec, dotProduct, Fintype.sum_sum_type, y,
      Finset.sum_neg_distrib] using hi
  have hG : Gp *ᵥ y = 0 := by
    funext i
    have hi := congrFun he (Sum.inr (Sum.inr i))
    simpa [kktMatrix, mulVec, dotProduct, Fintype.sum_sum_type, y,
      Finset.sum_neg_distrib] using hi
  have hd : y ⬝ᵥ (Q *ᵥ y) = 0 := by
    have hi := congrArg (fun w => y ⬝ᵥ w) htop
    simpa [dotProduct_add, dotProduct_mulVec, vecMul_transpose, hH, hG] using hi
  have hy : y = 0 := by
    by_contra hn
    have := hSSOSC y hn hG hH
    linarith
  have hbc := hLI b c (by simpa [hy] using htop)
  apply hv
  funext i
  rcases i with i | i
  · exact congrFun hy i
  · rcases i with i | i
    · exact congrFun hbc.1 i
    · exact congrFun hbc.2 i

#print axioms solution
