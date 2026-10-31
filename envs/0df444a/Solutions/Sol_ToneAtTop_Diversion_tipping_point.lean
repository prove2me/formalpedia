-- Prove2me | solution 1 for ToneAtTop.Diversion.tipping_point
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-30T20:59:50.277755+00:00
-- url     : https://prove2.me/submissions/64b4c476-5a61-4c2c-a6a5-1c1ca79501b4

import Mathlib
import Definitions.Def_ToneAtTop_Diversion_Model
open ToneAtTop.Diversion

theorem solution(P : Params) (hS : P.Standing) (c x : ℝ)
    (hc : c ∈ Set.Ico (0 : ℝ) 1) (hx : 0 ≤ x) :
    (Noncompliant P c x P.ηH ↔ tippingPoint P c < x) ∧
    (Noncompliant P c x 0 ↔ 0 < x) := by
  obtain ⟨hxb, hl, hp0, hp1, hβ, hγ0, hγ1, hη, htau⟩ := hS
  obtain ⟨hc0, hc1⟩ := hc
  have h1c : 0 < 1 - c := by linarith
  unfold Noncompliant utilCompliant utilNoncompliant tippingPoint Params.tau
  constructor
  · rw [div_lt_iff₀ h1c, div_lt_iff₀ hγ0]
    constructor <;> intro h <;> nlinarith
  · constructor <;> intro h
    · by_contra hx'
      push_neg at hx'
      have : x = 0 := le_antisymm hx' hx
      subst this
      simp at h
    · nlinarith [mul_pos (mul_pos hγ0 h1c) h]
