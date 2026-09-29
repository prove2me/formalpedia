-- Prove2me | solution 1 for WeylHeisenbergSIC.fiducial_d2_tetrahedron
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T23:41:19.353861+00:00
-- url     : https://prove2.me/submissions/d8ff6761-92e4-4b6f-9b57-f2288d4d61fd

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_WeylHeisenbergSIC_fiducial_d2_explicit

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem solution :
    ∃ ψ : ZMod 2 → ℂ,
      (∑ x : ZMod 2, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 2, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 2, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (2+1 : ℝ)⁻¹ := by
  exact WeylHeisenbergSIC.fiducial_d2_explicit
