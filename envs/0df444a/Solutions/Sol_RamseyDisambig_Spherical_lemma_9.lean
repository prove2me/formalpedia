-- Prove2me | solution 1 for RamseyDisambig.Spherical.lemma_9
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T19:03:10.296853+00:00
-- url     : https://prove2.me/submissions/159bc769-575c-4d02-a70a-76f40bc91376

import Mathlib
import Definitions.Def_RamseyDisambig_Spherical_GapColoring

section
set_option autoImplicit false

namespace RamseyDisambig.Dev.Pullback

open RamseyDisambig.Spherical

theorem le_finiteDiameter {X : Type*} [Finite X] (d : X → X → ℝ) (x y : X) :
    d x y ≤ finiteDiameter d := by
  unfold finiteDiameter
  haveI : Finite (X × X) := inferInstance
  exact le_csSup (Set.finite_range _).bddAbove ⟨(x, y), rfl⟩

theorem exists_eq_finiteDiameter {X : Type*} [Finite X] [Nonempty X] (d : X → X → ℝ) :
    ∃ x y, d x y = finiteDiameter d := by
  unfold finiteDiameter
  have hne : (Set.range (fun p : X × X => d p.1 p.2)).Nonempty := ⟨_, ⟨(Classical.arbitrary X, Classical.arbitrary X), rfl⟩⟩
  obtain ⟨⟨x, y⟩, h⟩ := Set.Nonempty.csSup_mem hne (Set.finite_range _)
  exact ⟨x, y, h⟩

/-- Lemma 9 for arbitrary nonnegative distance functions. -/
theorem pullback_gap {X Y : Type*} [Finite X] [Finite Y] (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (dX : X → X → ℝ) (dY : Y → Y → ℝ) (hY : ∀ y y', 0 ≤ dY y y')
    (ι₁ ι₂ : Y → X) (scale Δ : ℝ) (hscale0 : 0 ≤ scale) (hΔ : 0 ≤ Δ)
    (hscale : ∀ y y', dX (ι₁ y) (ι₂ y') = scale * dY y y' + Δ)
    (c : X → X → Bool) (hc : GapColoring ε dX c)
    (hdiam : (1 - ε / 2) * finiteDiameter dX ≤ scale * finiteDiameter dY) :
    GapColoring (ε / 2) dY (fun y y' => c (ι₁ y) (ι₂ y')) := by
  constructor
  all_goals intro y y' h
  all_goals
    have hYne : Nonempty Y := ⟨y⟩
    obtain ⟨u, v, huv⟩ := exists_eq_finiteDiameter dY
    have h1 : scale * finiteDiameter dY + Δ ≤ finiteDiameter dX := by
      rw [← huv, ← hscale]; exact le_finiteDiameter dX _ _
    have hDX : 0 ≤ finiteDiameter dX := by
      have := le_finiteDiameter dX (ι₁ y) (ι₂ y'); rw [hscale] at this
      have := hY y y'; nlinarith [hscale0, hΔ, mul_nonneg hscale0 (hY y y')]
    have hΔle : Δ ≤ ε / 2 * finiteDiameter dX := by nlinarith
  · apply hc.1
    rw [hscale]
    have : scale * dY y y' ≤ scale * (ε / 2 * finiteDiameter dY) := mul_le_mul_of_nonneg_left h hscale0
    nlinarith
  · apply hc.2
    rw [hscale]
    have : scale * ((1 - ε / 2) * finiteDiameter dY) ≤ scale * dY y y' :=
      mul_le_mul_of_nonneg_left h hscale0
    have h2 : (1 - ε / 2) * ((1 - ε / 2) * finiteDiameter dX) ≤ (1 - ε / 2) * (scale * finiteDiameter dY) :=
      mul_le_mul_of_nonneg_left hdiam (by linarith)
    nlinarith [mul_nonneg hε.le hDX]

end RamseyDisambig.Dev.Pullback
end

section
set_option autoImplicit false

namespace RamseyDisambig.Spherical

open RamseyDisambig.Spherical

theorem chk_lemma_9 {X Y : Type*} [MetricSpace X] [MetricSpace Y] [Finite X] [Finite Y]
    (ε : ℝ) (hε : 0 < ε) (hεhalf : ε < 1 / 2)
    (ι₁ ι₂ : Y → X) (scale Δ : ℝ) (hscale : 0 ≤ scale) (hΔ : 0 ≤ Δ)
    (hscale : ∀ y y', dist (ι₁ y) (ι₂ y') = scale * dist y y' + Δ)
    (c : X → X → Bool) (hc : GapColoring ε dist c)
    (hdiam : (1 - ε / 2) * finiteDiameter (dist : X → X → ℝ) ≤
      scale * finiteDiameter (dist : Y → Y → ℝ)) :
    GapColoring (ε / 2) dist (fun y y' => c (ι₁ y) (ι₂ y')) := by
  rename_i hs0
  exact Dev.Pullback.pullback_gap ε hε hεhalf dist dist (fun y y' => dist_nonneg) ι₁ ι₂ scale Δ hs0 hΔ hscale c hc hdiam

end RamseyDisambig.Spherical
end

theorem solution : type_of% @RamseyDisambig.Spherical.chk_lemma_9 := @RamseyDisambig.Spherical.chk_lemma_9
