-- Prove2me | solution 1 for WeylHeisenbergSIC.fiducial_d_ge_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-22T18:03:42.824243+00:00
-- url     : https://prove2.me/submissions/0c854136-664a-48b5-9fc3-d44b058fc095
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeylHeisenbergSIC_fiducial_exists_conjecture

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem solution (d : ℕ) [NeZero d] (hd : 3 ≤ d) :
    ∃ ψ : ZMod d → ℂ,
      (∑ x : ZMod d, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod d, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod d, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (d+1 : ℝ)⁻¹ := by
  exact WeylHeisenbergSIC.fiducial_exists_conjecture d
