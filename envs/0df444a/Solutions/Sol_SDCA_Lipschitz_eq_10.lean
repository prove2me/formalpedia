-- Prove2me | solution 1 for SDCA.Lipschitz.eq_10
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:16:15.367185+00:00
-- url     : https://prove2.me/submissions/ffdeb3e9-8cc9-462a-813a-08482e8b8596

import Mathlib
import Definitions.Def_SDCA_Lipschitz_Model

set_option autoImplicit false
open SDCA.Lipschitz

theorem sdl_conj_ne_bot (ψ : ℝ → ℝ) (u : ℝ) : conj ψ u ≠ ⊥ := by
  intro h
  have := le_iSup (fun z : ℝ => ((z * u - ψ z : ℝ) : EReal)) 0
  have h' : (⨆ z : ℝ, ((z * u - ψ z : ℝ) : EReal)) = ⊥ := h
  rw [h'] at this
  exact absurd (le_bot_iff.mp this) (EReal.coe_ne_bot _)

theorem sdl_conj_real (ψ : ℝ → ℝ) (u : ℝ) (h : conj ψ u ≠ ⊤) : ∃ c : ℝ, conj ψ u = (c : EReal) := by
  lift conj ψ u to ℝ using ⟨h, sdl_conj_ne_bot ψ u⟩ with c hc
  exact ⟨c, rfl⟩

/-- Fenchel equality at a subgradient. -/
theorem sdl_conj_subgrad (ψ : ℝ → ℝ) (a g : ℝ) (h : ∀ z : ℝ, ψ a + g * (z - a) ≤ ψ z) :
    conj ψ g = ((a * g - ψ a : ℝ) : EReal) := by
  apply le_antisymm
  · unfold conj
    refine iSup_le (fun z => ?_)
    rw [EReal.coe_le_coe_iff]
    have := h z
    linarith
  · exact le_iSup (fun z : ℝ => ((z * g - ψ z : ℝ) : EReal)) a

theorem sdl_norm_expand {d : ℕ} (w y : EuclideanSpace ℝ (Fin d)) (c δ : ℝ) :
    ‖w + c • (δ • y)‖ ^ 2 = ‖w‖ ^ 2 + 2 * (c * δ) * inner ℝ w y + (c * δ) ^ 2 * ‖y‖ ^ 2 := by
  rw [norm_add_sq_real, inner_smul_right, inner_smul_right, norm_smul, norm_smul, mul_pow, mul_pow,
    Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  ring

theorem solution {d n : ℕ} (φ : Fin n → ℝ → ℝ) (x : Fin n → EuclideanSpace ℝ (Fin d)) (lam : ℝ)
    (hn : 0 < n) (hlam : 0 < lam) (hconv : ∀ i, ConvexOn ℝ Set.univ (φ i))
    (Δ : (Fin n → ℝ) → Fin n → ℝ) (hΔ : IsSDCAStep φ x lam Δ)
    (α : Fin n → ℝ) (hα : ∀ j, conj (φ j) (-α j) ≠ ⊤) (i : Fin n)
    (γ : ℝ) (hγ : 0 ≤ γ)
    (hsc : ∀ (u v r : ℝ), 0 ≤ r → r ≤ 1 →
      conj (φ i) (r * u + (1 - r) * v) ≤
        ((r : ℝ) : EReal) * conj (φ i) u + ((1 - r : ℝ) : EReal) * conj (φ i) v
          - ((γ * r * (1 - r) / 2 * (u - v) ^ 2 : ℝ) : EReal))
    (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (u : ℝ) (hu : -u ∈ subdiff (φ i) (inner ℝ (wOf x lam α) (x i))) :
    coordObj φ x lam α i (Δ α i) - coordObj φ x lam α i 0 ≥
      ((s : ℝ) : EReal) *
        (((φ i (inner ℝ (wOf x lam α) (x i)) + α i * inner ℝ (wOf x lam α) (x i)
            + (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 : ℝ) : EReal)
          + conj (φ i) (-α i)) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hln : lam * n ≠ 0 := by positivity
  set w := wOf x lam α with hw
  set a : ℝ := inner ℝ w (x i) with ha
  obtain ⟨c0, hc0⟩ := sdl_conj_real _ _ (hα i)
  have hcu : conj (φ i) (-u) = ((a * (-u) - φ i a : ℝ) : EReal) := sdl_conj_subgrad _ a (-u) hu
  set δ : ℝ := s * (u - α i) with hδ
  -- strong convexity at r = s
  have hsc' := hsc (-u) (-α i) s hs0 hs1
  have harg : s * -u + (1 - s) * -α i = -(α i + δ) := by rw [hδ]; ring
  rw [harg, hcu, hc0] at hsc'
  -- the right side is a real number
  have hR1 : conj (φ i) (-(α i + δ)) ≤
      ((s * (a * (-u) - φ i a) + (1 - s) * c0 - γ * s * (1 - s) / 2 * (u - α i) ^ 2 : ℝ) : EReal) := by
    refine hsc'.trans (le_of_eq ?_)
    have : ((-u) - (-α i)) ^ 2 = (u - α i) ^ 2 := by ring
    rw [this]
    simp only [EReal.coe_sub, EReal.coe_add, EReal.coe_mul]
  obtain ⟨c2, hc2⟩ := sdl_conj_real (φ i) (-(α i + δ))
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) hR1)
  rw [hc2, EReal.coe_le_coe_iff] at hR1
  -- coordinate objective at δ and at 0
  have hobjδ : coordObj φ x lam α i δ =
      ((-c2 - lam * n / 2 * ‖w + (1 / (lam * n)) • (δ • x i)‖ ^ 2 : ℝ) : EReal) := by
    unfold coordObj
    rw [hc2, ← hw, ← EReal.coe_neg, ← EReal.coe_sub]
  have hobj0 : coordObj φ x lam α i 0 = ((-c0 - lam * n / 2 * ‖w‖ ^ 2 : ℝ) : EReal) := by
    unfold coordObj
    simp only [add_zero, zero_smul, smul_zero]
    rw [hc0, ← hw, ← EReal.coe_neg, ← EReal.coe_sub]
  have hmax := hΔ α i δ
  have h1 : coordObj φ x lam α i (Δ α i) - coordObj φ x lam α i 0 ≥
      coordObj φ x lam α i δ - coordObj φ x lam α i 0 := by
    rw [sub_eq_add_neg, sub_eq_add_neg]
    exact add_le_add hmax le_rfl
  refine le_trans ?_ h1
  rw [hobjδ, hobj0, ← EReal.coe_sub]
  have hrhs : ((s : ℝ) : EReal) *
        (((φ i a + α i * a
            + (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 : ℝ) : EReal)
          + conj (φ i) (-α i)) =
      ((s * ((φ i a + α i * a
            + (γ * (1 - s) / 2 - s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2) + c0) : ℝ) : EReal) := by
    rw [hc0, ← EReal.coe_add, ← EReal.coe_mul]
  rw [hrhs, EReal.coe_le_coe_iff]
  rw [sdl_norm_expand w (x i) (1 / (lam * n)) δ]
  have hδa : δ = s * (u - α i) := rfl
  have e1 : lam * n / 2 * (‖w‖ ^ 2 + 2 * (1 / (lam * n) * δ) * a + (1 / (lam * n) * δ) ^ 2 * ‖x i‖ ^ 2)
      = lam * n / 2 * ‖w‖ ^ 2 + δ * a + δ ^ 2 * ‖x i‖ ^ 2 / (2 * lam * n) := by
    field_simp
  rw [e1]
  have e2 : (s * (u - α i)) ^ 2 * ‖x i‖ ^ 2 / (2 * lam * n) =
      s * (s * ‖x i‖ ^ 2 / (2 * lam * n)) * (u - α i) ^ 2 := by ring
  rw [hδa] at *
  rw [e2]
  linarith [hR1]
