-- Prove2me | solution 1 for OnlineTaxiRouting.Integrality.eq15_of_fixed
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T13:46:54.336439+00:00
-- url     : https://prove2.me/submissions/35ce2e44-05a5-4dd1-b1de-fbabb35f0b01

import Mathlib
import Definitions.Def_OnlineTaxiRouting_Integrality_Setting
set_option autoImplicit false
open OnlineTaxiRouting.Integrality

theorem solution {C K : Type*} (I : Instance C K)
    (hfix : ∀ c, I.tmin c = I.tmax c) (v : Var C K) :
    ((∀ c, I.tmin c ≤ v.2.2.2 c ∧ v.2.2.2 c ≤ I.tmax c) ↔ v.2.2.2 = I.tmin) ∧
    (v.2.2.2 = I.tmin → ∀ c c',
      ((I.tmin c - I.tmax c') + (I.T c' c - (I.tmin c - I.tmax c')) * v.1 c' c
          ≤ v.2.2.2 c - v.2.2.2 c' ↔
        (I.T c' c - (I.tmin c - I.tmin c')) * v.1 c' c ≤ 0)) := by
  constructor
  · constructor
    · intro h
      funext c
      have := h c
      rw [← hfix c] at this
      exact le_antisymm this.2 this.1
    · intro h c
      rw [h, ← hfix c]
      exact ⟨le_refl _, le_refl _⟩
  · intro h c c'
    rw [h, ← hfix c']
    constructor <;> intro h' <;> nlinarith [h']
