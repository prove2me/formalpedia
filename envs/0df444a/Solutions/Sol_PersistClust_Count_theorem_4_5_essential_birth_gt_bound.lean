-- Prove2me | solution 1 for PersistClust.Count.theorem_4_5_essential_birth_gt_bound
-- status  : ACCEPTED   (prove)
-- author  : @fabianroll
-- created : 2026-10-12T17:11:20.993986+00:00
-- url     : https://prove2.me/submissions/01bb4a81-f6e8-48a1-9ad7-a501f824bef3

import Mathlib
import Definitions.Def_PersistClust_Count_Setting
import Definitions.Def_PersistClust_Count_Diagram
import Definitions.Def_PersistClust_Count_Rips

open PersistClust.Count

/- Every essential bar of a separated diagram is born strictly above d₂: the
DeltaN d₁ branch would need a death coordinate below bottom (impossible), so the
LamE d₂ branch gives d₂ < b. (The same fact appears in the auxiliary layer of
the accepted theorem_4_8_core solution lineage.) -/
theorem q2_essential_birth_gt {X : Type*} [MetricSpace X] {f : X → ℝ} {d₁ d₂ : ℝ} (hsep : IsSeparated (diagram0 f) d₁ d₂) {b : EReal}
    (hb : diagram0 f (b, ⊥) ≠ 0) : (d₂ : EReal) < b := by
  have hpoint : diagram0 f ((b : EReal), (⊥ : EReal)) ≠ 0 := hb
  rcases hsep ((b : EReal), (⊥ : EReal)) hpoint with hN | hS
  · have hp : ((b : EReal), (⊥ : EReal)) ∈ DeltaN d₁ ↔
        ((b : EReal), (⊥ : EReal)).1 - ((d₁ : ℝ) : EReal) < ((b : EReal), (⊥ : EReal)).2 := Iff.rfl
    rw [hp] at hN
    rw [show ((b : EReal), (⊥ : EReal)).2 = (⊥ : EReal) from rfl] at hN
    exact absurd hN not_lt_bot
  · have hmem : ((b : EReal), (⊥ : EReal)) ∈ LamE d₂ ↔
        ((d₂ : ℝ) : EReal) < ((b : EReal), (⊥ : EReal)).1 := Iff.rfl
    rw [hmem] at hS
    simpa using hS.2

theorem solution {X : Type*} [MetricSpace X] {f : X → ℝ} {d₁ d₂ : ℝ} (hsep : IsSeparated (diagram0 f) d₁ d₂) {Δ : ℝ} (hΔd : Δ < d₂)
    {b : EReal} (hb : diagram0 f (b, ⊥) ≠ 0) (hble : b ≤ (((Δ : ℝ) : ℝ) : EReal)) :
    False := by
  have hbgt : (d₂ : EReal) < (((Δ : ℝ) : ℝ) : EReal) :=
    lt_of_lt_of_le (q2_essential_birth_gt hsep hb) hble
  exact absurd (EReal.coe_lt_coe_iff.mp hbgt) (not_lt.mpr hΔd.le)
