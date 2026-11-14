-- Prove2me | solution 1 for ZeroFreeRRG.Hardcore.proposition_2_8
-- status  : ACCEPTED   (prove)
-- author  : @wcysai
-- created : 2026-11-13T06:17:54.37305+00:00
-- url     : https://prove2.me/submissions/0da3221d-7416-4709-8574-5d093b9ec85f

import Mathlib
set_option autoImplicit false
open Set

theorem solution (D S : Set ℂ) (f g : ℂ → ℂ) (z₀ : ℂ)
    (hopen : IsOpen D) (hconnected : IsConnected D)
    (hf : DifferentiableOn ℂ f D) (hg : DifferentiableOn ℂ g D)
    (hSD : S ⊆ D) (hz : z₀ ∈ D) (hacc : z₀ ∈ closure (S \ {z₀}))
    (heq : ∀ z ∈ S, f z = g z) : EqOn f g D := by
  have hsub : S \ {z₀} ⊆ {z | f z = g z} \ {z₀} := by
    intro z hz'
    exact ⟨heq z hz'.1, hz'.2⟩
  exact (hf.analyticOnNhd hopen).eqOn_of_preconnected_of_mem_closure
    (hg.analyticOnNhd hopen) hconnected.isPreconnected hz (closure_mono hsub hacc)
