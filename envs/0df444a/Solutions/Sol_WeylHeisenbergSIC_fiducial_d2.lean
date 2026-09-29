-- Prove2me | solution 1 for WeylHeisenbergSIC.fiducial_d2
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T23:39:06.975053+00:00
-- url     : https://prove2.me/submissions/ae9efc9a-c29d-4e6f-96ab-312761bdac54

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_WeylHeisenbergSIC_fiducial_d2_tetrahedron

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem solution :
    ∃ ψ : ZMod 2 → ℂ,
      (∑ x : ZMod 2, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 2, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 2, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (2+1 : ℝ)⁻¹ := by
  exact WeylHeisenbergSIC.fiducial_d2_tetrahedron
