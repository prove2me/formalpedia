-- Prove2me | solution 1 for OTDRO.Dual.sup_transport_eq_ellRob
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-05T10:04:58.330028+00:00
-- url     : https://prove2.me/submissions/a5233c02-9b80-4511-a0fb-fd853aa472f0

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
  set s := Real.sqrt δ with hs_def
  have hs : 0 < s := Real.sqrt_pos.2 hδ
  have hss : s ^ 2 = δ := Real.sq_sqrt hδ.le
  have hls : 0 ≤ lam / s := div_nonneg hlam hs.le
  have hD : ∀ Δ : EuclideanSpace ℝ (Fin d), 0 ≤ dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp) := by
    intro Δ
    by_cases h : Δ.ofLp = 0
    · simp [h]
    · simpa using (hQ.dotProduct_mulVec_pos h).le
  unfold OTDRO.Dual.ellRob OTDRO.Dual.Fobj
  by_cases hβ : β = 0
  · subst hβ
    have hq : OTDRO.Dual.quadInv A 0 x = 0 := by simp [OTDRO.Dual.quadInv]
    simp only [hq, inner_zero_left, mul_zero, add_zero, zero_sub, mul_neg, mul_one, sub_neg_eq_add]
    rw [ciSup_const]
    apply le_antisymm
    · refine iSup_le fun Δ => EReal.coe_le_coe_iff.2 ?_
      have := hD Δ
      have : lam / s * δ = lam * s := by rw [← hss]; field_simp
      nlinarith [mul_nonneg hls (hD Δ)]
    · refine le_iSup_of_le 0 (EReal.coe_le_coe_iff.2 (le_of_eq ?_))
      have : lam / s * δ = lam * s := by rw [← hss]; field_simp
      simp; linarith
  · have hβv : β.ofLp ≠ 0 := by
      intro h; apply hβ; exact WithLp.ofLp_injective _ (by simpa using h)
    set q := OTDRO.Dual.quadInv A β x with hq_def
    have hq : 0 < q := by
      simpa [hq_def, OTDRO.Dual.quadInv] using hQ.inv.dotProduct_mulVec_pos hβv
    have hmin := OTDRO.Dual.inf_quad_hyperplane (A x) hQ β hβ
    apply le_antisymm
    · refine iSup_le fun Δ => ?_
      set c := inner ℝ β Δ with hc
      refine le_iSup_of_le (c / (s * q)) (EReal.coe_le_coe_iff.2 ?_)
      have hlow : c ^ 2 / q ≤ dotProduct Δ.ofLp (A x *ᵥ Δ.ofLp) :=
        (hmin c).2 ⟨Δ, hc.symm, rfl⟩
      have e1 : c / (s * q) * s * q = c := by field_simp
      have e2 : lam * s * ((c / (s * q)) ^ 2 * q - 1) = lam / s * (c ^ 2 / q - δ) := by
        rw [← hss]; field_simp
      rw [inner_add_right, e1, e2]
      have := mul_le_mul_of_nonneg_left (sub_le_sub_right hlow δ) hls
      unfold OTDRO.Dual.quadInv at *
      linarith
    · refine iSup_le fun γ => ?_
      obtain ⟨⟨Δ, hΔc, hΔq⟩, -⟩ := hmin (γ * s * q)
      refine le_iSup_of_le Δ (EReal.coe_le_coe_iff.2 (le_of_eq ?_))
      rw [inner_add_right, hΔc, ← hΔq]
      have e2 : lam * s * (γ ^ 2 * q - 1) = lam / s * ((γ * s * q) ^ 2 / q - δ) := by
        rw [← hss]; field_simp
      rw [e2, ← hs_def]
      rfl
