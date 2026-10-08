-- Prove2me | solution 1 for RobinsonSR.NLP.schur_posdef
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T21:53:15.441898+00:00
-- url     : https://prove2.me/submissions/1f95a052-6594-42c1-841a-a13f410e4749

import Mathlib
import Definitions.Def_RobinsonSR_NLP_Setting
open scoped RealInnerProductSpace Matrix
open Matrix
open RobinsonSR.NLP
set_option autoImplicit false

private theorem nonsingular {ιn ιq ιr : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
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

theorem solution {ιn ιq ιr ιs : Type*} [Fintype ιn] [Fintype ιq] [Fintype ιr]
    [Fintype ιs] [DecidableEq ιn] [DecidableEq ιq] [DecidableEq ιr]
    (Q : Matrix ιn ιn ℝ) (H : Matrix ιq ιn ℝ) (Gp : Matrix ιr ιn ℝ) (G0 : Matrix ιs ιn ℝ)
    (hQ : Q.IsSymm)
    (hSSOSC : ∀ y : ιn → ℝ, y ≠ 0 → Gp *ᵥ y = 0 → H *ᵥ y = 0 → 0 < y ⬝ᵥ (Q *ᵥ y))
    (hLI : ∀ (b : ιq → ℝ) (c : ιr → ℝ) (d : ιs → ℝ),
      Hᵀ *ᵥ b + Gpᵀ *ᵥ c + G0ᵀ *ᵥ d = 0 → b = 0 ∧ c = 0 ∧ d = 0) :
    RobinsonSR.Schur.PosDefNS (schurS Q H Gp G0) := by
  classical
  have hdet := nonsingular Q H Gp hSSOSC (fun b c he => by
    have hh := hLI b c 0 (by simpa using he)
    exact ⟨hh.1, hh.2.1⟩)
  intro z hz
  let R := zeroRowBlock (ιq := ιq) (ιr := ιr) G0
  let K := kktMatrix Q H Gp
  let v := K⁻¹ *ᵥ (Rᵀ *ᵥ z)
  let y : ιn → ℝ := fun i => v (Sum.inl i)
  let b : ιq → ℝ := fun i => v (Sum.inr (Sum.inl i))
  let c : ιr → ℝ := fun i => v (Sum.inr (Sum.inr i))
  have he : K *ᵥ v = Rᵀ *ᵥ z := by
    dsimp [v]
    rw [mulVec_mulVec, mul_nonsing_inv K (isUnit_iff_ne_zero.mpr hdet), one_mulVec]
  have htop : Q *ᵥ y + (Hᵀ *ᵥ b + Gpᵀ *ᵥ c) = G0ᵀ *ᵥ z := by
    funext i
    have hi := congrFun he (Sum.inl i)
    simpa [K, R, zeroRowBlock, kktMatrix, mulVec, dotProduct, Fintype.sum_sum_type,
      y, b, c, Finset.sum_add_distrib] using hi
  have hH : H *ᵥ y = 0 := by
    funext i
    have hi := congrFun he (Sum.inr (Sum.inl i))
    simpa [K, R, zeroRowBlock, kktMatrix, mulVec, dotProduct, Fintype.sum_sum_type, y,
      Finset.sum_neg_distrib] using hi
  have hG : Gp *ᵥ y = 0 := by
    funext i
    have hi := congrFun he (Sum.inr (Sum.inr i))
    simpa [K, R, zeroRowBlock, kktMatrix, mulVec, dotProduct, Fintype.sum_sum_type, y,
      Finset.sum_neg_distrib] using hi
  have hy : y ≠ 0 := by
    intro hy
    have hh : Hᵀ *ᵥ b + Gpᵀ *ᵥ c + G0ᵀ *ᵥ (-z) = 0 := by
      simpa [hy, mulVec_neg, sub_eq_add_neg] using sub_eq_zero.mpr htop
    have hd := (hLI b c (-z) hh).2.2
    exact hz (neg_eq_zero.mp hd)
  have hd : y ⬝ᵥ (Q *ᵥ y) = z ⬝ᵥ (G0 *ᵥ y) := by
    have hi := congrArg (fun w => y ⬝ᵥ w) htop
    simp only [dotProduct_add, dotProduct_mulVec, vecMul_transpose, hH, hG,
      zero_dotProduct, add_zero] at hi
    rw [dotProduct_comm (G0 *ᵥ y) z] at hi
    simpa only [dotProduct_mulVec] using hi
  have hs : schurS Q H Gp G0 *ᵥ z = G0 *ᵥ y := by
    change (R * K⁻¹ * Rᵀ) *ᵥ z = _
    rw [← mulVec_mulVec, ← mulVec_mulVec]
    change R *ᵥ v = _
    funext i
    simp [R, zeroRowBlock, mulVec, dotProduct, Fintype.sum_sum_type, y]
  rw [hs, ← hd]
  exact hSSOSC y hy hG hH

#print axioms solution
