-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_separated_bar_death_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T17:13:23.112692+00:00
-- url     : https://prove2.me/submissions/0004f5b1-6f9c-489e-8c60-f363e7ebd924

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count

theorem solution {X : Type*} [MetricSpace X] {f : X → ℝ} {d₁ d₂ : ℝ} (hsep : IsSeparated (diagram0 f) d₁ d₂) {Δ : ℝ} (hΔd : Δ < d₂)
    {b d : EReal} (hbar : diagram0 f (b, d) ≠ 0) (hble : b ≤ (((Δ : ℝ) : ℝ) : EReal)) :
    b - (((d₁ : ℝ) : ℝ) : EReal) < d := by
  rcases hsep ((b, d) : EReal × EReal) hbar with hN | hS
  · have hmem : ((b, d) : EReal × EReal) ∈ DeltaN d₁ ↔
        ((b, d) : EReal × EReal).1 - ((d₁ : ℝ) : EReal) < ((b, d) : EReal × EReal).2 := Iff.rfl
    rw [hmem] at hN
    exact hN
  · exfalso
    have hmem : ((b, d) : EReal × EReal) ∈ LamE d₂ ↔
        ((d₂ : ℝ) : EReal) < ((b, d) : EReal × EReal).1 := Iff.rfl
    rw [hmem] at hS
    have hs2 : (d₂ : EReal) < b := by simpa using hS.2
    have hp2 : (d₂ : EReal) < (((Δ : ℝ) : ℝ) : EReal) := lt_of_lt_of_le hs2 hble
    exact absurd (EReal.coe_lt_coe_iff.mp hp2) (not_lt.mpr hΔd.le)
