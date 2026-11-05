-- Prove2me | solution 1 for ShortWDRODual.Legendre.lemma_3
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-04T12:20:25.910386+00:00
-- url     : https://prove2.me/submissions/21854876-b2af-4f57-ae9e-dab3840b15f8

import Mathlib
import Definitions.Def_ShortWDRODual_Legendre_Setting

open ShortWDRODual.Legendre

namespace WDRO1L3

/-- Right three-slope inequality: `l < a < μ`, `a = (1-t) l + t μ`. -/
lemma three_slope_right {l a μ g ga gμ : ℝ} (h1 : l < a) (h2 : a < μ)
    (h : ga ≤ (1 - (a - l) / (μ - l)) * g + ((a - l) / (μ - l)) * gμ) :
    ga - (g - ga) / (a - l) * (μ - a) ≤ gμ := by
  have hm : 0 < μ - l := by linarith
  have hal : 0 < a - l := by linarith
  have e1 : (1 - (a - l) / (μ - l)) = (μ - a) / (μ - l) := by field_simp; ring
  rw [e1] at h
  have h' : ga * (μ - l) ≤ (μ - a) * g + (a - l) * gμ := by
    have := mul_le_mul_of_nonneg_right h hm.le
    have e2 : ((μ - a) / (μ - l) * g + (a - l) / (μ - l) * gμ) * (μ - l)
        = (μ - a) * g + (a - l) * gμ := by field_simp
    linarith
  rw [← sub_nonneg]
  have : gμ - (ga - (g - ga) / (a - l) * (μ - a)) = ((μ - a) * g + (a - l) * gμ - ga * (μ - l)) / (a - l) := by
    field_simp; ring
  rw [this]
  apply div_nonneg _ hal.le
  linarith

lemma coe_conv (t x z : ℝ) :
    ((1 - t : ℝ) : EReal) * (x : EReal) + ((t : ℝ) : EReal) * (z : EReal) =
      (((1 - t) * x + t * z : ℝ) : EReal) := by
  rw [EReal.coe_add, EReal.coe_mul, EReal.coe_mul]

lemma real_of {e : EReal} (h1 : e ≠ ⊤) (h2 : e ≠ ⊥) : e = ((e.toReal : ℝ) : EReal) :=
  (EReal.coe_toReal h1 h2).symm

end WDRO1L3

open WDRO1L3

theorem solution (h : ℝ → EReal)
    (h_nbot : ∀ ρ, h ρ ≠ ⊥)
    (h_anti : Antitone h)
    (h_conv : ∀ a b t : ℝ, 0 ≤ t → t ≤ 1 →
      h ((1 - t) * a + t * b) ≤ ((1 - t : ℝ) : EReal) * h a + ((t : ℝ) : EReal) * h b)
    (h_neg : ∀ ρ : ℝ, ρ < 0 → h ρ = ⊤)
    (h_proper : ∃ ρ : ℝ, h ρ ≠ ⊤) :
    LowerSemicontinuous (fun lam : ℝ => legendre h (-lam)) ∧
    Antitone (fun lam : ℝ => legendre h (-lam)) ∧
    (∀ a b t : ℝ, 0 ≤ t → t ≤ 1 →
      legendre h (-((1 - t) * a + t * b)) ≤
        ((1 - t : ℝ) : EReal) * legendre h (-a) + ((t : ℝ) : EReal) * legendre h (-b)) ∧
    (∀ lam : ℝ, lam < 0 → legendre h (-lam) = ⊤) ∧
    (∃ lam : ℝ, legendre h lam ≠ ⊤) := by
  obtain ⟨ρ0, hρ0⟩ := h_proper
  have hρ0nn : 0 ≤ ρ0 := by
    by_contra hlt; push_neg at hlt; exact hρ0 (h_neg ρ0 hlt)
  set T : ℝ → ℝ → EReal := fun ρ lam => ((-lam * ρ : ℝ) : EReal) - h ρ with hT
  have hF : ∀ lam, legendre h (-lam) = ⨆ ρ, T ρ lam := fun lam => rfl
  have hTtop : ∀ ρ lam, h ρ = ⊤ → T ρ lam = ⊥ := by
    intro ρ lam hh; simp only [hT]; rw [hh, EReal.sub_top]
  have hTfin : ∀ ρ lam, h ρ ≠ ⊤ → T ρ lam = ((-lam * ρ - (h ρ).toReal : ℝ) : EReal) := by
    intro ρ lam hh
    simp only [hT]
    rw [real_of hh (h_nbot ρ), ← EReal.coe_sub, EReal.toReal_coe]
  have hfin_ge : ∀ ρ, ρ0 ≤ ρ → h ρ ≠ ⊤ := fun ρ hρ => ne_top_of_le_ne_top hρ0 (h_anti hρ)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- lower semicontinuity
    have : (fun lam : ℝ => legendre h (-lam)) = fun lam => ⨆ ρ, T ρ lam := funext hF
    rw [this]
    refine lowerSemicontinuous_iSup fun ρ => ?_
    by_cases hh : h ρ = ⊤
    · have : T ρ = fun _ => ⊥ := funext fun lam => hTtop ρ lam hh
      rw [this]; exact lowerSemicontinuous_const
    · have : T ρ = fun lam => ((-lam * ρ - (h ρ).toReal : ℝ) : EReal) :=
        funext fun lam => hTfin ρ lam hh
      rw [this]
      exact (continuous_coe_real_ereal.comp (by fun_prop)).lowerSemicontinuous
  · -- antitone
    intro a b hab
    simp only [hF]
    refine iSup_mono fun ρ => ?_
    by_cases hh : h ρ = ⊤
    · rw [hTtop ρ b hh]; exact bot_le
    · have hρ : 0 ≤ ρ := by by_contra hlt; push_neg at hlt; exact hh (h_neg ρ hlt)
      rw [hTfin ρ a hh, hTfin ρ b hh]
      exact_mod_cast (by nlinarith : -b * ρ - (h ρ).toReal ≤ -a * ρ - (h ρ).toReal)
  · -- convexity
    intro a b t ht0 ht1
    rcases ht0.lt_or_eq with ht0' | ht0'
    swap
    · subst ht0'; simp
    rcases ht1.lt_or_eq with ht1' | ht1'
    swap
    · subst ht1'; simp
    rw [hF ((1 - t) * a + t * b)]
    refine iSup_le fun ρ => ?_
    by_cases hh : h ρ = ⊤
    · rw [hTtop ρ _ hh]; exact bot_le
    have h1t : (0 : EReal) ≤ ((1 - t : ℝ) : EReal) := by exact_mod_cast (by linarith : (0:ℝ) ≤ 1 - t)
    have ht : (0 : EReal) ≤ ((t : ℝ) : EReal) := by exact_mod_cast ht0
    have hle : T ρ ((1 - t) * a + t * b) ≤
        ((1 - t : ℝ) : EReal) * T ρ a + ((t : ℝ) : EReal) * T ρ b := by
      rw [hTfin ρ _ hh, hTfin ρ _ hh, hTfin ρ _ hh, coe_conv]
      exact_mod_cast le_of_eq (by ring)
    refine hle.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (by rw [hF]; exact le_iSup (fun ρ => T ρ a) ρ) h1t
    · exact mul_le_mul_of_nonneg_left (by rw [hF]; exact le_iSup (fun ρ => T ρ b) ρ) ht
  · -- `+∞` for `λ < 0`
    intro lam hlam
    rw [hF]
    refine eq_top_iff.mpr (le_of_forall_lt fun y hy => ?_)
    induction y using EReal.rec with
    | bot => exact lt_of_lt_of_le (EReal.bot_lt_coe _) (le_iSup_of_le ρ0 (by
        rw [hTfin ρ0 lam hρ0]))
    | top => exact absurd hy (lt_irrefl _)
    | coe y =>
      set g0 := (h ρ0).toReal
      set ρ := ρ0 + (|y| + |g0| + |lam * ρ0| + 1) / (-lam) with hρ
      have hlpos : 0 < -lam := by linarith
      have hρge : ρ0 ≤ ρ := by
        have : 0 ≤ (|y| + |g0| + |lam * ρ0| + 1) / (-lam) := by positivity
        linarith
      refine lt_of_lt_of_le ?_ (le_iSup_of_le ρ le_rfl)
      rw [hTfin ρ lam (hfin_ge ρ hρge)]
      have hhρ : (h ρ).toReal ≤ g0 := by
        have := h_anti hρge
        rw [real_of (hfin_ge ρ hρge) (h_nbot ρ), real_of hρ0 (h_nbot ρ0)] at this
        exact_mod_cast this
      have hkey : -lam * ρ = -lam * ρ0 + (|y| + |g0| + |lam * ρ0| + 1) := by
        rw [hρ, mul_add, mul_div_cancel₀ _ hlpos.ne']
      have : y < -lam * ρ - (h ρ).toReal := by
        rw [hkey]
        have h1 := le_abs_self y
        have h2 := le_abs_self g0
        have h3 := le_abs_self (lam * ρ0)
        have h4 : -lam * ρ0 = -(lam * ρ0) := by ring
        linarith
      exact_mod_cast this
  · -- properness of the conjugate
    set q := ρ0 + 1 with hq
    have hqfin : h q ≠ ⊤ := hfin_ge q (by linarith)
    set g0 := (h ρ0).toReal
    set gq := (h q).toReal
    have hgq_le : gq ≤ g0 := by
      have := h_anti (show ρ0 ≤ q by linarith)
      rw [real_of hqfin (h_nbot q), real_of hρ0 (h_nbot ρ0)] at this
      exact_mod_cast this
    set s := gq - g0 with hs
    have hs0 : s ≤ 0 := by linarith
    refine ⟨s, ne_top_of_le_ne_top (EReal.coe_ne_top (-gq)) ?_⟩
    unfold legendre
    refine iSup_le fun ρ => ?_
    by_cases hh : h ρ = ⊤
    · rw [hh, EReal.sub_top]; exact bot_le
    have hρ : 0 ≤ ρ := by by_contra hlt; push_neg at hlt; exact hh (h_neg ρ hlt)
    rw [real_of hh (h_nbot ρ), ← EReal.coe_sub]
    -- lower affine bound `h ρ ≥ gq + s ρ`
    have hbound : gq + s * ρ ≤ (h ρ).toReal := by
      rcases le_or_gt ρ q with hρq | hρq
      · have := h_anti hρq
        rw [real_of hh (h_nbot ρ), real_of hqfin (h_nbot q)] at this
        have : gq ≤ (h ρ).toReal := by exact_mod_cast this
        nlinarith
      · set t := (q - ρ0) / (ρ - ρ0) with ht
        have hpμ : 0 < ρ - ρ0 := by linarith
        have ht0 : 0 ≤ t := div_nonneg (by linarith) hpμ.le
        have ht1 : t ≤ 1 := by rw [ht, div_le_one hpμ]; linarith
        have hpt : (1 - t) * ρ0 + t * ρ = q := by rw [ht]; field_simp; ring
        have hc := h_conv ρ0 ρ t ht0 ht1
        rw [hpt, real_of hqfin (h_nbot q), real_of hρ0 (h_nbot ρ0), real_of hh (h_nbot ρ),
          coe_conv] at hc
        have hc' : gq ≤ (1 - (q - ρ0) / (ρ - ρ0)) * g0 + ((q - ρ0) / (ρ - ρ0)) * (h ρ).toReal := by
          exact_mod_cast hc
        have h3 := three_slope_right (by linarith : ρ0 < q) hρq hc'
        have hqp : q - ρ0 = 1 := by rw [hq]; ring
        rw [hqp, div_one] at h3
        nlinarith
    exact_mod_cast (by linarith : s * ρ - (h ρ).toReal ≤ -gq)
