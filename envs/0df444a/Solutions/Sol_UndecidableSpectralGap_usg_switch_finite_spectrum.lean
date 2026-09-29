-- Prove2me | solution 1 for UndecidableSpectralGap.usg_switch_finite_spectrum
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-22T18:17:48.14308+00:00
-- url     : https://prove2.me/submissions/c284c4b6-8e58-4f68-acd1-40cb7ad079c2

import Theorems.Thm_UndecidableSpectralGap_usg_switch_local_strength
import Theorems.Thm_UndecidableSpectralGap_usg_switch_sector_spectrum_bounds
import Theorems.Thm_UndecidableSpectralGap_usg_switch_magnon_inclusion
import Theorems.Thm_UndecidableSpectralGap_usg_switch_positive_gap

set_option autoImplicit false
open UndecidableSpectralGap

theorem solution
    (b a : ℝ) (hb : 0 < b) (hbhalf : b ≤ 1 / 2) (ha : |a| ≤ b) :
    localInteractionStrength ((a : ℂ) • switchProjector)
      (switchGuard + (b : ℂ) • switchExchange) switchGuard ≤ 1 ∧
    ∀ L : ℕ, 2 ≤ L →
      (0 ∈ specReal (switchHam L a b) ∧
       a * (L : ℝ) ^ 2 ∈ specReal (switchHam L a b) ∧
       ∀ μ ∈ specReal (switchHam L a b), min 0 (a * (L : ℝ) ^ 2) ≤ μ) ∧
      (∀ s ∈ switchMagnonSpectrum L b,
        a * (L : ℝ) ^ 2 + s ∈ specReal (switchHam L a b)) ∧
      (1 ≤ a * (L : ℝ) ^ 2 → eigMultiplicity (switchHam L a b) 0 = 1 ∧
        ∀ μ ∈ specReal (switchHam L a b), μ ≠ 0 → 1 ≤ μ) := by
  refine ⟨UndecidableSpectralGap.usg_switch_local_strength b a hb hbhalf ha, ?_⟩
  intro L hL
  exact
    ⟨UndecidableSpectralGap.usg_switch_sector_spectrum_bounds b a hb hbhalf ha L hL,
     UndecidableSpectralGap.usg_switch_magnon_inclusion b a hb hbhalf ha L hL,
     UndecidableSpectralGap.usg_switch_positive_gap b a hb hbhalf ha L hL⟩
