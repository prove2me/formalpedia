-- Prove2me | solution 1 for WeylHeisenbergSIC.fiducial_d_ge_2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T23:35:56.48339+00:00
-- url     : https://prove2.me/submissions/93f7b856-9881-4b35-8f26-f17bd3360dce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_WeylHeisenbergSIC_fiducial_d2
import Theorems.Thm_WeylHeisenbergSIC_fiducial_d_ge_3

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem solution (d : ℕ) [NeZero d] (hd : 2 ≤ d) :
    ∃ ψ : ZMod d → ℂ,
      (∑ x : ZMod d, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod d, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod d, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (d+1 : ℝ)⁻¹ := by
  by_cases h2 : d = 2
  · subst h2
    rcases WeylHeisenbergSIC.fiducial_d2 with ⟨ψ, hnorm, hfid⟩
    refine ⟨ψ, hnorm, fun a b hab => ?_⟩
    have heq : ((2 : ℕ) + 1 : ℝ) = (2 + 1 : ℝ) := by norm_num
    rw [heq]
    exact hfid a b hab
  · have hge3 : 3 ≤ d := by omega
    exact WeylHeisenbergSIC.fiducial_d_ge_3 d hge3
