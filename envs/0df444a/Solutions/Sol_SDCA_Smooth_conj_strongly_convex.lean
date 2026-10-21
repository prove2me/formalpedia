-- Prove2me | solution 1 for SDCA.Smooth.conj_strongly_convex
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T23:47:34.98218+00:00
-- url     : https://prove2.me/submissions/aafad4d5-5bbb-461f-b349-682d49292914

import Mathlib
import Definitions.Def_SDCA_Smooth_conj

set_option autoImplicit false
open SDCA.Lipschitz (conj)

theorem sds_conj_ne_bot (ψ : ℝ → ℝ) (u : ℝ) : conj ψ u ≠ ⊥ := by
  intro h
  have := le_iSup (fun z : ℝ => ((z * u - ψ z : ℝ) : EReal)) 0
  have h' : (⨆ z : ℝ, ((z * u - ψ z : ℝ) : EReal)) = ⊥ := h
  rw [h'] at this
  exact absurd (le_bot_iff.mp this) (EReal.coe_ne_bot _)

/-- descent lemma for a function with `(1/γ)`-Lipschitz derivative. -/
theorem sds_descent (φ φ' : ℝ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hderiv : ∀ a : ℝ, HasDerivAt φ (φ' a) a)
    (hsmooth : ∀ a b : ℝ, |φ' a - φ' b| ≤ (1 / γ) * |a - b|) (z y : ℝ) :
    φ y ≤ φ z + φ' z * (y - z) + (y - z) ^ 2 / (2 * γ) := by
  set h : ℝ → ℝ := fun t => φ t - φ' z * (t - z) - (t - z) * (t - z) / (2 * γ) with hh
  have hd : ∀ t, HasDerivAt h (φ' t - φ' z - (t - z) / γ) t := by
    intro t
    have h1 := hderiv t
    have h2 : HasDerivAt (fun t : ℝ => φ' z * (t - z)) (φ' z) t := by
      simpa using ((hasDerivAt_id t).sub_const z).const_mul (φ' z)
    have h3 : HasDerivAt (fun t : ℝ => (t - z) * (t - z) / (2 * γ)) ((t - z) / γ) t := by
      have h4 := (((hasDerivAt_id t).sub_const z).mul ((hasDerivAt_id t).sub_const z)).div_const (2 * γ)
      refine h4.congr_deriv ?_
      simp only [id]
      field_simp
      ring
    exact (h1.sub h2).sub h3
  have hcont : Continuous h := continuous_iff_continuousAt.2 (fun t => (hd t).continuousAt)
  have hdiff : Differentiable ℝ h := fun t => (hd t).differentiableAt
  have hderivh : ∀ t, deriv h t = φ' t - φ' z - (t - z) / γ := fun t => (hd t).deriv
  have key : h y ≤ h z := by
    rcases le_total z y with hzy | hyz
    · have := antitoneOn_of_deriv_nonpos (convex_Ici z) hcont.continuousOn
        hdiff.differentiableOn (fun t ht => by
          rw [interior_Ici] at ht
          have ht' : z < t := ht
          rw [hderivh]
          have h6 := hsmooth t z
          rw [abs_of_pos (by linarith : (0:ℝ) < t - z)] at h6
          have h5 := (abs_le.mp h6).2
          have : (t - z) / γ = 1 / γ * (t - z) := by ring
          linarith)
      exact this (Set.mem_Ici.2 le_rfl) (Set.mem_Ici.2 hzy) hzy
    · have := monotoneOn_of_deriv_nonneg (convex_Iic z) hcont.continuousOn
        hdiff.differentiableOn (fun t ht => by
          rw [interior_Iic] at ht
          have ht' : t < z := ht
          rw [hderivh]
          have h6 := hsmooth t z
          rw [abs_of_neg (by linarith : t - z < 0)] at h6
          have h5 := (abs_le.mp h6).1
          have : (t - z) / γ = 1 / γ * (t - z) := by ring
          linarith)
      exact this (Set.mem_Iic.2 hyz) (Set.mem_Iic.2 le_rfl) hyz
  simp only [hh] at key
  simp at key
  rw [sq]
  linarith

theorem sds_conj_ge (φ φ' : ℝ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hderiv : ∀ a : ℝ, HasDerivAt φ (φ' a) a)
    (hsmooth : ∀ a b : ℝ, |φ' a - φ' b| ≤ (1 / γ) * |a - b|) (u z : ℝ) :
    (((z * u - φ z + γ / 2 * (u - φ' z) ^ 2 : ℝ)) : EReal) ≤ conj φ u := by
  refine le_trans ?_ (le_iSup (fun y : ℝ => ((y * u - φ y : ℝ) : EReal)) (z + γ * (u - φ' z)))
  rw [EReal.coe_le_coe_iff]
  have := sds_descent φ φ' γ hγ hderiv hsmooth z (z + γ * (u - φ' z))
  rw [show z + γ * (u - φ' z) - z = γ * (u - φ' z) by ring] at this
  rw [show (γ * (u - φ' z)) ^ 2 / (2 * γ) = γ / 2 * (u - φ' z) ^ 2 by field_simp] at this
  nlinarith

theorem solution (φ φ' : ℝ → ℝ) (γ : ℝ) (hγ : 0 < γ)
    (hconv : ConvexOn ℝ Set.univ φ)
    (hderiv : ∀ a : ℝ, HasDerivAt φ (φ' a) a)
    (hsmooth : ∀ a b : ℝ, |φ' a - φ' b| ≤ (1 / γ) * |a - b|) :
    ∀ u v : ℝ, ∀ s ∈ Set.Icc (0 : ℝ) 1,
      -SDCA.Lipschitz.conj φ (s * u + (1 - s) * v) ≥
        -(((s : ℝ) : EReal) * SDCA.Lipschitz.conj φ u) - ((1 - s : ℝ) : EReal) * SDCA.Lipschitz.conj φ v +
          ((γ * s * (1 - s) / 2 * (u - v) ^ 2 : ℝ) : EReal) := by
  intro u v s hs
  obtain ⟨hs0, hs1⟩ := hs
  rcases hs0.eq_or_lt with h0 | h0
  · subst h0
    simp
  rcases hs1.eq_or_lt with h1 | h1
  · subst h1
    simp
  -- 0 < s < 1
  have hs' : 0 < 1 - s := by linarith
  by_cases hu : conj φ u = ⊤
  · have : -(((s : ℝ) : EReal) * conj φ u) - ((1 - s : ℝ) : EReal) * conj φ v +
        ((γ * s * (1 - s) / 2 * (u - v) ^ 2 : ℝ) : EReal) = ⊥ := by
      rw [hu, EReal.coe_mul_top_of_pos h0, EReal.neg_top, EReal.bot_sub, EReal.bot_add]
    rw [this]; exact bot_le
  by_cases hv : conj φ v = ⊤
  · have : -(((s : ℝ) : EReal) * conj φ u) - ((1 - s : ℝ) : EReal) * conj φ v +
        ((γ * s * (1 - s) / 2 * (u - v) ^ 2 : ℝ) : EReal) = ⊥ := by
      obtain ⟨cu, hcu⟩ : ∃ c : ℝ, conj φ u = c := by
        lift conj φ u to ℝ using ⟨hu, sds_conj_ne_bot _ _⟩ with c hc
        exact ⟨c, rfl⟩
      rw [hv, hcu, EReal.coe_mul_top_of_pos hs', ← EReal.coe_mul, ← EReal.coe_neg]
      rw [EReal.sub_top]
      exact EReal.bot_add _
    rw [this]; exact bot_le
  obtain ⟨cu, hcu⟩ : ∃ c : ℝ, conj φ u = c := by
    lift conj φ u to ℝ using ⟨hu, sds_conj_ne_bot _ _⟩ with c hc
    exact ⟨c, rfl⟩
  obtain ⟨cv, hcv⟩ : ∃ c : ℝ, conj φ v = c := by
    lift conj φ v to ℝ using ⟨hv, sds_conj_ne_bot _ _⟩ with c hc
    exact ⟨c, rfl⟩
  have hbound : conj φ (s * u + (1 - s) * v) ≤
      ((s * cu + (1 - s) * cv - γ * s * (1 - s) / 2 * (u - v) ^ 2 : ℝ) : EReal) := by
    refine iSup_le (fun z => ?_)
    rw [EReal.coe_le_coe_iff]
    have h1 := sds_conj_ge φ φ' γ hγ hderiv hsmooth u z
    have h2 := sds_conj_ge φ φ' γ hγ hderiv hsmooth v z
    rw [hcu, EReal.coe_le_coe_iff] at h1
    rw [hcv, EReal.coe_le_coe_iff] at h2
    have hg : 0 ≤ γ / 2 * (s * (u - φ' z) ^ 2 + (1 - s) * (v - φ' z) ^ 2 -
        s * (1 - s) * (u - v) ^ 2) := by
      have : s * (u - φ' z) ^ 2 + (1 - s) * (v - φ' z) ^ 2 - s * (1 - s) * (u - v) ^ 2 =
          (s * u + (1 - s) * v - φ' z) ^ 2 := by ring
      rw [this]; positivity
    nlinarith [mul_le_mul_of_nonneg_left h1 hs0, mul_le_mul_of_nonneg_left h2 hs'.le]
  have hrhs : -(((s : ℝ) : EReal) * conj φ u) - ((1 - s : ℝ) : EReal) * conj φ v +
        ((γ * s * (1 - s) / 2 * (u - v) ^ 2 : ℝ) : EReal) =
      ((-(s * cu + (1 - s) * cv - γ * s * (1 - s) / 2 * (u - v) ^ 2) : ℝ) : EReal) := by
    rw [hcu, hcv, ← EReal.coe_mul, ← EReal.coe_mul, ← EReal.coe_neg, ← EReal.coe_sub,
      ← EReal.coe_add]
    congr 1; ring
  rw [ge_iff_le, hrhs, EReal.coe_neg, EReal.neg_le_neg_iff]
  exact hbound
