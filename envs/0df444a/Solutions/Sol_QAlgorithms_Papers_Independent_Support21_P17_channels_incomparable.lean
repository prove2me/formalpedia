-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Support21.P17.channels_incomparable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T05:01:18.887058+00:00
-- url     : https://prove2.me/submissions/d1a1ea6b-bb89-46c9-a271-51864e49333a

import Definitions.Def_QAlgorithms_Papers_Independent_Support21_P17
noncomputable section

open scoped ComplexConjugate ComplexOrder Matrix Kronecker Topology TensorProduct

open Filter

namespace QAlgorithms.Papers.Independent.Support21.P17

attribute [local instance] Classical.propDecidable

attribute [local instance] Classical.decEq

open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)

open QAlgorithms.Papers.Independent.Next46.P33 (UltraweakTest)

open QAlgorithms.Papers.Independent.Next46.P32 (PositiveKernel)

open QAlgorithms.Papers.Independent.Information100.P50 (M Lin coefficientMap)

end QAlgorithms.Papers.Independent.Support21.P17

end

open QAlgorithms.Papers.Independent.Support21.P17
open QAlgorithms.Papers.Independent.Claimed50.P50 (NoiseSpace completedTensorMap)
open scoped ComplexConjugate
lemma g66j_lin_zero (α c : ℝ) (h : ∀ s : ℝ, 0 ≤ s * α + c) : α = 0 := by
  by_contra hα
  have h1 := h (-(|c| + 1) / α)
  rw [div_mul_cancel₀ _ hα] at h1
  linarith [le_abs_self c]

lemma g66j_cplx_zero (u v c : ℂ)
    (h : ∀ t : ℂ, (conj t * u + t * v + c).im = 0 ∧ 0 ≤ (conj t * u + t * v + c).re) :
    u = 0 := by
  have hr : u.re + v.re = 0 := by
    apply g66j_lin_zero _ c.re
    intro s
    have := (h (s : ℂ)).2
    simp at this; nlinarith [this]
  have hi : u.im - v.im = 0 := by
    apply g66j_lin_zero _ c.re
    intro s
    have := (h ((s : ℂ) * Complex.I)).2
    simp at this; nlinarith [this]
  have h0 := (h 0).1
  have h1 := (h 1).1
  have hI := (h Complex.I).1
  simp at h0 h1 hI
  apply Complex.ext <;> simp <;> nlinarith

lemma g66j_gram_zero {A : Type*} [CStarAlgebra A] {H : SeparableHilbertSpace}
    (Φ : A →ₗ[ℂ] HilbertEndomorphism H) (hΦ : GramCompletelyPositive Φ) (h1 : Φ 1 = 0) :
    Φ = 0 := by
  ext a η
  have key : ∀ ξ : H, inner ℂ ξ (Φ a η) = 0 := by
    intro ξ
    apply g66j_cplx_zero _ (inner ℂ η (Φ (star a) ξ)) (inner ℂ η (Φ (star a * a) η))
    intro t
    have := hΦ 2 ![1, a] ![t • ξ, η]
    simp only [Fin.sum_univ_two] at this
    simp [h1, inner_smul_left, inner_smul_right, map_smul, mul_comm] at this ⊢
    constructor <;> linarith [this.1, this.2]
  have := key (Φ a η)
  rw [inner_self_eq_zero] at this
  simpa using this

/-- Proposition 4.1, PDF p.12: channels are incomparable in CP order.
The independent norm proof in the remark avoids the defective Theorem 3.5. -/
theorem solution (H K : SeparableHilbertSpace) (S T : HilbertEndomorphism H →ₗ[ℂ] HilbertEndomorphism K)
    (hS : IsUnitalNormalCP S) (hT : IsUnitalNormalCP T) : CompletelyDominated S T ↔ S = T := by
  constructor
  · intro h
    have h0 : T - S = 0 := by
      apply g66j_gram_zero _ h
      show T (ContinuousLinearMap.id ℂ H) - S (ContinuousLinearMap.id ℂ H) = 0
      rw [hS.2, hT.2, sub_self]
    exact (sub_eq_zero.1 h0).symm
  · rintro rfl
    unfold CompletelyDominated
    rw [sub_self]
    intro n a eta
    simp
