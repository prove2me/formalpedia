-- Prove2me | solution 1 for WeylHeisenbergSIC.fiducial_d1
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T23:32:49.674647+00:00
-- url     : https://prove2.me/submissions/6e35485f-8b3b-4e55-bfb8-d9dd3a8d91e6

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem solution :
    ∃ ψ : ZMod 1 → ℂ,
      (∑ x : ZMod 1, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod 1, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod 1, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (1+1 : ℝ)⁻¹ := by
  use (fun _ => 1)
  constructor
  · have h : (Finset.univ : Finset (ZMod 1)) = {0} := rfl
    rw [h, Finset.sum_singleton]
    simp
  · intro a b hab
    exfalso
    have ha : a = 0 := Subsingleton.elim a 0
    have hb : b = 0 := Subsingleton.elim b 0
    subst ha hb
    exact hab rfl
