-- Prove2me | solution 1 for QAlgorithms.Papers.Independent.Claimed50.P50.unital_minimal_uniqueness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-21T09:47:41.153386+00:00
-- url     : https://prove2.me/submissions/26c10a60-2953-453f-9709-4f6652708e6e

import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P50
noncomputable section

open QAlgorithms.Papers.Independent.Claimed50.P50

open scoped TensorProduct BigOperators

variable {H N : Type*}

variable [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

variable [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]

lemma g68m_lin_nonneg (x y : ℝ) (h : ∀ r : ℝ, 0 ≤ r * x + y) : x = 0 := by
  by_contra hx
  have := h (-(y + 1) / x)
  rw [div_mul_cancel₀ _ hx] at this
  linarith

lemma g68m_quad (a b c : ℂ)
    (h : ∀ s : ℂ, ((starRingEnd ℂ) s * a + s * b + c).im = 0 ∧
      0 ≤ ((starRingEnd ℂ) s * a + s * b + c).re) : a = 0 := by
  have h1 := h 1
  have h0 := h 0
  have hI := h Complex.I
  simp at h1 h0 hI
  have hre : a.re + b.re = 0 := by
    apply g68m_lin_nonneg _ c.re
    intro r
    have := (h (r : ℂ)).2
    simp at this
    linarith
  have him : a.im - b.im = 0 := by
    apply g68m_lin_nonneg _ c.re
    intro r
    have := (h ((r : ℂ) * Complex.I)).2
    simp at this
    linarith
  apply Complex.ext
  · simp; linarith [h1.1, hI.1, h0.1]
  · simp; linarith [h1.1, hI.1, h0.1]

lemma g68m_cp_zero (F : (H →L[ℂ] H) → (H →L[ℂ] H)) (hF : IsCPOnBoundedOperators F)
    (h1 : ∀ v : H, inner ℂ v (F (ContinuousLinearMap.id ℂ H) v) = 0) (Y : H →L[ℂ] H) :
    F Y = 0 := by
  have key : ∀ v1 v2 : H, inner ℂ v1 (F Y v2) = 0 := by
    intro v1 v2
    apply g68m_quad (inner ℂ v1 (F Y v2)) (inner ℂ v2 (F Y.adjoint v1))
      (inner ℂ v2 (F (Y.adjoint.comp Y) v2))
    intro s
    have := hF 2 ![s • v1, v2] ![ContinuousLinearMap.id ℂ H, Y]
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      ContinuousLinearMap.adjoint_id, ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_id,
      inner_smul_left, map_smul, inner_smul_right, h1, mul_zero, zero_add] at this
    convert this using 2 <;> ring_nf
  ext v
  have := key (F Y v) v
  rw [inner_self_eq_zero] at this
  simpa using this

theorem solution {D : Submodule ℂ H}
    (hDense : Dense (D : Set H)) (S : StandardData (N := N) D)
    (hConservative : IsConservativeForm S)
    (hK : HasMaximalAccretiveClosure S) (Phi : DynamicalSemigroup H)
    (hMinimal : IsMinimalBackward S Phi) (hUnital : IsUnitalQDS Phi) :
    ∀ Psi : DynamicalSemigroup H, SolvesBackward S Psi →
      ∀ (t : NNReal) (X : H →L[ℂ] H), Psi.maps t X = Phi.maps t X := by
  intro Psi hPsi t X
  have hCP := hMinimal.2 Psi hPsi t
  have h1 : ∀ v : H, inner ℂ v ((fun X => Psi.maps t X - Phi.maps t X)
      (ContinuousLinearMap.id ℂ H) v) = 0 := by
    intro v
    have hc := hCP 1 ![v] ![ContinuousLinearMap.id ℂ H]
    simp only [Fin.sum_univ_one, Matrix.cons_val_zero, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.id_comp] at hc
    have hs := Psi.subunital t v
    simp only [hUnital t] at hc ⊢
    simp only [ContinuousLinearMap.sub_apply, inner_sub_right] at hc hs ⊢
    apply Complex.ext
    · simp only [Complex.sub_re, Complex.zero_re] at hc hs ⊢; linarith [hc.2, hs.2]
    · simpa using hc.1
  have := g68m_cp_zero _ hCP h1 X
  exact sub_eq_zero.mp this

end
