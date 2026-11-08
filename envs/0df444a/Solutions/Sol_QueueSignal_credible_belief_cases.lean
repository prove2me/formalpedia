-- Prove2me | solution 1 for QueueSignal.credible_belief_cases
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-08T05:51:56.054995+00:00
-- url     : https://prove2.me/submissions/3bd8da62-8f9b-4b67-92e5-b16016539d27

import Mathlib
import Definitions.Def_QueueSignal_SignalingGame

open QueueSignal in
theorem solution (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (pay : QType → Sig → ℝ → ℝ) (σ : Profile) (b : Sig → ℝ) (s : Sig) (hs : ¬ OnPath σ s)
    (γ : ℝ) :
    (IsCredible δ pay σ b s γ →
      (∀ t, eqPay pay σ b t < pay t s γ) → γ = δ) ∧
    (IsCredible δ pay σ b s γ →
      eqPay pay σ b .H ≤ pay .H s γ → pay .L s γ < eqPay pay σ b .L → γ = 1) ∧
    (IsCredible δ pay σ b s γ →
      eqPay pay σ b .L ≤ pay .L s γ → pay .H s γ < eqPay pay σ b .H → γ = 0) ∧
    ((∀ t, pay t s γ < eqPay pay σ b t) → ¬ IsCredible δ pay σ b s γ) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro ⟨_, h, h1, _, _, _, hγ⟩ hall
    rw [hγ, h1 .H (hall .H), h1 .L (hall .L)]
    simp only [prior, mul_one]
    rw [show δ + (1 - δ) = 1 by ring, div_one]
  · rintro ⟨_, h, _, _, h3, hpos, hγ⟩ _ hL
    have hL0 : h .L = 0 := h3 .L (not_lt.mpr hL.le) hL.ne
    have hHpos : 0 < h .H := by linarith
    rw [hγ, hL0]
    simp only [prior, mul_zero, add_zero]
    exact div_self (mul_pos hδ0 hHpos).ne'
  · rintro ⟨_, h, _, _, h3, _, hγ⟩ _ hH
    have hH0 : h .H = 0 := h3 .H (not_lt.mpr hH.le) hH.ne
    rw [hγ, hH0]
    simp only [prior, mul_zero, zero_div]
  · rintro hall ⟨⟨t, ht⟩, _⟩
    rcases ht with ht | ht
    · linarith [hall t]
    · linarith [hall t]
