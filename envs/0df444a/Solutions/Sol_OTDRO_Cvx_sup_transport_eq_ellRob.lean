-- Prove2me | solution 1 for OTDRO.Cvx.sup_transport_eq_ellRob
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T09:19:56.765351+00:00
-- url     : https://prove2.me/submissions/a96d41bb-e2f0-4e19-9b3f-3c99e8515a0e

import Mathlib
import Definitions.Def_OTDRO_Dual_Setting
import Theorems.Thm_OTDRO_Dual_inf_quad_hyperplane

open Matrix

theorem solution {d : ℕ}
    (A : EuclideanSpace ℝ (Fin d) → Matrix (Fin d) (Fin d) ℝ)
    (x : EuclideanSpace ℝ (Fin d)) (hQ : (A x).PosDef)
    (ℓ : ℝ → ℝ) (δ : ℝ) (hδ : 0 < δ)
    (β : EuclideanSpace ℝ (Fin d)) (lam : ℝ) (hlam : 0 ≤ lam) :
    (⨆ Δ : EuclideanSpace ℝ (Fin d),
      ((ℓ (inner ℝ β (x + Δ)) - (lam / Real.sqrt δ) *
        (dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp) - δ) : ℝ) : EReal)) =
      OTDRO.Dual.ellRob ℓ A δ β lam x := by
  obtain ⟨s, hs, rfl⟩ : ∃ s, 0 < s ∧ δ = s ^ 2 :=
    ⟨Real.sqrt δ, Real.sqrt_pos.2 hδ, (Real.sq_sqrt hδ.le).symm⟩
  have hsq : Real.sqrt (s ^ 2) = s := Real.sqrt_sq hs.le
  have hunit : IsUnit (A x).det := (Matrix.isUnit_iff_isUnit_det (A x)).1 hQ.isUnit
  have hQv : A x *ᵥ ((A x)⁻¹ *ᵥ β.ofLp) = β.ofLp := by
    simp [mulVec_mulVec, mul_nonsing_inv _ hunit]
  have hinner : ∀ y : EuclideanSpace ℝ (Fin d), inner ℝ β y = β.ofLp ⬝ᵥ y.ofLp := fun y => by
    rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]; simp
  unfold OTDRO.Dual.ellRob OTDRO.Dual.Fobj OTDRO.Dual.quadInv
  simp only [hsq]
  apply le_antisymm
  · apply iSup_le; intro Δ
    have h0 : 0 ≤ Δ.ofLp ⬝ᵥ (A x *ᵥ Δ.ofLp) := by
      simpa using hQ.posSemidef.dotProduct_mulVec_nonneg Δ.ofLp
    rw [inner_add_right]
    by_cases hβ : β = 0
    · subst hβ
      refine le_trans ?_ (le_iSup _ (0:ℝ))
      apply EReal.coe_le_coe_iff.2
      simp only [inner_zero_left, add_zero, WithLp.ofLp_zero, zero_dotProduct, mul_zero,
        zero_mul, zero_sub, mul_neg, mul_one, sub_neg_eq_add]
      have : (lam / s) * (Δ.ofLp ⬝ᵥ (A x *ᵥ Δ.ofLp) - s ^ 2) ≥ - (lam * s) := by
        have e : lam * s = lam / s * s ^ 2 := by
          field_simp
        rw [e]; nlinarith [div_nonneg hlam hs.le]
      linarith
    · set q := β.ofLp ⬝ᵥ ((A x)⁻¹ *ᵥ β.ofLp) with hqdef
      have hq : 0 < q := by
        have hb : β.ofLp ≠ 0 := by
          intro h; apply hβ; simpa using congrArg (WithLp.toLp 2) h
        simpa using hQ.inv.dotProduct_mulVec_pos hb
      set c := inner ℝ β Δ with hc
      have hmin := (OTDRO.Dual.inf_quad_hyperplane (A x) hQ β hβ c).2 ⟨Δ, rfl, rfl⟩
      refine le_trans ?_ (le_iSup _ (c / (s * q)))
      apply EReal.coe_le_coe_iff.2
      have hγ : c / (s * q) * s * q = c := by field_simp
      rw [hγ]
      have e : lam * s * ((c / (s * q)) ^ 2 * q - 1)
          = lam / s * (c ^ 2 / q - s ^ 2) := by
        field_simp
      rw [e]
      have hmin' : c ^ 2 / q ≤ Δ.ofLp ⬝ᵥ (A x *ᵥ Δ.ofLp) := hmin
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right hmin' (s ^ 2)) (div_nonneg hlam hs.le)
      linarith
  · apply iSup_le; intro γ
    refine le_trans ?_ (le_iSup _ (WithLp.toLp 2 ((γ * s) • ((A x)⁻¹ *ᵥ β.ofLp))))
    apply EReal.coe_le_coe_iff.2
    apply le_of_eq
    have h1 : inner ℝ β (WithLp.toLp 2 ((γ * s) • ((A x)⁻¹ *ᵥ β.ofLp)) :
        EuclideanSpace ℝ (Fin d)) = γ * s * (β.ofLp ⬝ᵥ ((A x)⁻¹ *ᵥ β.ofLp)) := by
      rw [hinner]; simp [dotProduct_smul]
    have h2 : (WithLp.toLp 2 ((γ * s) • ((A x)⁻¹ *ᵥ β.ofLp)) :
        EuclideanSpace ℝ (Fin d)).ofLp ⬝ᵥ (A x *ᵥ (WithLp.toLp 2 ((γ * s) •
          ((A x)⁻¹ *ᵥ β.ofLp)) : EuclideanSpace ℝ (Fin d)).ofLp)
        = (γ * s) ^ 2 * (β.ofLp ⬝ᵥ ((A x)⁻¹ *ᵥ β.ofLp)) := by
      simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, hQv,
        smul_eq_mul]
      rw [dotProduct_comm ((A x)⁻¹ *ᵥ β.ofLp) β.ofLp]; ring
    rw [inner_add_right, h1, h2]
    generalize β.ofLp ⬝ᵥ ((A x)⁻¹ *ᵥ β.ofLp) = q
    have h3 : lam / s * ((γ * s) ^ 2 * q - s ^ 2)
        = lam * s * (γ ^ 2 * q - 1) := by
      field_simp
    rw [h3]
