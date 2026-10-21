-- Prove2me | solution 1 for SDCA.Smooth.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:26:24.693974+00:00
-- url     : https://prove2.me/submissions/008cd98d-fb15-4e35-bb99-73e35db315ac

import Mathlib
import Definitions.Def_SDCA_Smooth_Model

set_option autoImplicit false
open scoped InnerProductSpace
open SDCA.Smooth
open SDCA.Lipschitz (conj)

theorem sds_conj_ne_bot (ψ : ℝ → ℝ) (u : ℝ) : conj ψ u ≠ ⊥ := by
  intro h
  have := le_iSup (fun z : ℝ => ((z * u - ψ z : ℝ) : EReal)) 0
  have h' : (⨆ z : ℝ, ((z * u - ψ z : ℝ) : EReal)) = ⊥ := h
  rw [h'] at this
  exact absurd (le_bot_iff.mp this) (EReal.coe_ne_bot _)

theorem sds_conj_real (ψ : ℝ → ℝ) (u : ℝ) (h : conj ψ u ≠ ⊤) : ∃ c : ℝ, conj ψ u = (c : EReal) := by
  lift conj ψ u to ℝ using ⟨h, sds_conj_ne_bot ψ u⟩ with c hc
  exact ⟨c, rfl⟩

/-- Fenchel equality at a subgradient. -/
theorem sds_conj_subgrad (ψ : ℝ → ℝ) (a g : ℝ) (h : ∀ z : ℝ, ψ a + g * (z - a) ≤ ψ z) :
    conj ψ g = ((a * g - ψ a : ℝ) : EReal) := by
  apply le_antisymm
  · unfold conj
    refine iSup_le (fun z => ?_)
    rw [EReal.coe_le_coe_iff]
    have := h z
    linarith
  · exact le_iSup (fun z : ℝ => ((z * g - ψ z : ℝ) : EReal)) a

theorem sds_norm_expand {d : ℕ} (w y : EuclideanSpace ℝ (Fin d)) (c δ : ℝ) :
    ‖w + c • (δ • y)‖ ^ 2 = ‖w‖ ^ 2 + 2 * (c * δ) * inner ℝ w y + (c * δ) ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, inner_smul_right, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

theorem solution {d n : ℕ} (hn : 0 < n) (x : Fin n → EuclideanSpace ℝ (Fin d))
    (φ : Fin n → ℝ → ℝ) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (lam : ℝ) (hlam : 0 < lam)
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep lam x φ Δ)
    (α : Fin n → ℝ) (i : Fin n) (hfeas : SDCA.Lipschitz.conj (φ i) (-α i) ≠ ⊤)
    (γ : ℝ) (hγ : 0 ≤ γ) (hsc : ConjStronglyConvex (φ i) γ)
    (u : ℝ)
    (hu : ∀ z : ℝ, φ i ⟪wOf lam x α, x i⟫_ℝ + (-u) * (z - ⟪wOf lam x α, x i⟫_ℝ) ≤ φ i z)
    (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    coordObj lam x φ α i (Δ α i) - coordObj lam x φ α i 0 ≥
      ((s : ℝ) : EReal) *
        (((φ i ⟪wOf lam x α, x i⟫_ℝ : ℝ) : EReal) + SDCA.Lipschitz.conj (φ i) (-α i) +
          ((α i * ⟪wOf lam x α, x i⟫_ℝ +
              (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 : ℝ) : EReal)) := by
  obtain ⟨hs0, hs1⟩ := hs
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hln : lam * n ≠ 0 := by positivity
  set w := wOf lam x α with hw
  set a : ℝ := ⟪w, x i⟫_ℝ with ha
  obtain ⟨c0, hc0⟩ := sds_conj_real _ _ hfeas
  have hcu : conj (φ i) (-u) = ((a * (-u) - φ i a : ℝ) : EReal) := sds_conj_subgrad _ a (-u) hu
  set δ : ℝ := s * (u - α i) with hδ
  -- strong convexity at r = s
  have hsc0 := hsc (-u) (-α i) s ⟨hs0, hs1⟩
  have harg : s * -u + (1 - s) * -α i = -(α i + δ) := by rw [hδ]; ring
  rw [harg, hcu, hc0] at hsc0
  have hreal : -(((s : ℝ) : EReal) * ((a * (-u) - φ i a : ℝ) : EReal)) -
      ((1 - s : ℝ) : EReal) * (c0 : EReal) +
        ((γ * s * (1 - s) / 2 * (-u - -α i) ^ 2 : ℝ) : EReal) =
      ((-(s * (a * (-u) - φ i a)) - (1 - s) * c0 + γ * s * (1 - s) / 2 * (-u - -α i) ^ 2 : ℝ) : EReal) := by
    simp only [EReal.coe_sub, EReal.coe_add, EReal.coe_mul, EReal.coe_neg]
  rw [hreal] at hsc0
  have hsc1 : conj (φ i) (-(α i + δ)) ≤
      ((-(-(s * (a * (-u) - φ i a)) - (1 - s) * c0 + γ * s * (1 - s) / 2 * (-u - -α i) ^ 2) : ℝ) : EReal) := by
    have := EReal.neg_le_neg_iff.mpr hsc0
    rw [neg_neg, ← EReal.coe_neg] at this
    exact this
  -- the right side is a real number
  have hR1 : conj (φ i) (-(α i + δ)) ≤
      ((s * (a * (-u) - φ i a) + (1 - s) * c0 - γ * s * (1 - s) / 2 * (u - α i) ^ 2 : ℝ) : EReal) := by
    refine hsc1.trans (le_of_eq ?_)
    congr 1
    have : ((-u) - (-α i)) ^ 2 = (u - α i) ^ 2 := by ring
    rw [this]; ring
  obtain ⟨c2, hc2⟩ := sds_conj_real (φ i) (-(α i + δ))
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) hR1)
  rw [hc2, EReal.coe_le_coe_iff] at hR1
  -- coordinate objective at δ and at 0
  have hobjδ : coordObj lam x φ α i δ =
      ((-c2 - lam * n / 2 * ‖w + (lam * n)⁻¹ • (δ • x i)‖ ^ 2 : ℝ) : EReal) := by
    unfold coordObj
    rw [hc2, ← hw, ← EReal.coe_neg, ← EReal.coe_sub]
  have hobj0 : coordObj lam x φ α i 0 = ((-c0 - lam * n / 2 * ‖w‖ ^ 2 : ℝ) : EReal) := by
    unfold coordObj
    simp only [add_zero, zero_smul, smul_zero]
    rw [hc0, ← hw, ← EReal.coe_neg, ← EReal.coe_sub]
  have hmax := hΔ α i δ
  have h1 : coordObj lam x φ α i (Δ α i) - coordObj lam x φ α i 0 ≥
      coordObj lam x φ α i δ - coordObj lam x φ α i 0 := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add hmax le_rfl
  refine le_trans ?_ h1
  rw [hobjδ, hobj0, ← EReal.coe_sub]
  have hrhs : ((s : ℝ) : EReal) *
        (((φ i a : ℝ) : EReal) + conj (φ i) (-α i) +
          ((α i * a + (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 : ℝ) : EReal)) =
      ((s * (φ i a + c0 + (α i * a
            + (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2)) : ℝ) : EReal) := by
    rw [hc0, ← EReal.coe_add, ← EReal.coe_add, ← EReal.coe_mul]
  rw [hrhs, EReal.coe_le_coe_iff]
  rw [sds_norm_expand w (x i) ((lam * n)⁻¹) δ]
  have hδa : δ = s * (u - α i) := rfl
  have e1 : lam * n / 2 * (‖w‖ ^ 2 + 2 * ((lam * n)⁻¹ * δ) * a + ((lam * n)⁻¹ * δ) ^ 2 * ‖x i‖ ^ 2)
      = lam * n / 2 * ‖w‖ ^ 2 + δ * a + δ ^ 2 * ‖x i‖ ^ 2 / (2 * lam * n) := by
    field_simp
  rw [e1]
  have e2 : (s * (u - α i)) ^ 2 * ‖x i‖ ^ 2 / (2 * lam * n) =
      s * (s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 := by ring
  rw [hδa] at *
  rw [e2]
  linarith [hR1]
