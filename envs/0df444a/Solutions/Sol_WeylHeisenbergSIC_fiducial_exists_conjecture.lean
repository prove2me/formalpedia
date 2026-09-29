-- Prove2me | solution 1 for WeylHeisenbergSIC.fiducial_exists_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-21T23:31:54.078165+00:00
-- url     : https://prove2.me/submissions/76dc08a2-9250-42ac-9416-00bd2efeef84
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.Analysis.InnerProductSpace.PiL2
import Theorems.Thm_WeylHeisenbergSIC_fiducial_d1
import Theorems.Thm_WeylHeisenbergSIC_fiducial_d_ge_2

set_option autoImplicit false
noncomputable section
open scoped BigOperators

theorem solution (d : ℕ) [NeZero d] :
    ∃ ψ : ZMod d → ℂ,
      (∑ x : ZMod d, Complex.normSq (ψ x)) = 1 ∧
      ∀ a b : ZMod d, (a,b) ≠ (0,0) →
        Complex.normSq (∑ x : ZMod d, star (ψ x) *
          (ZMod.stdAddChar (b*x) * ψ (x+a))) = (d+1 : ℝ)⁻¹ := by
  by_cases hd : d = 1
  · subst hd
    rcases WeylHeisenbergSIC.fiducial_d1 with ⟨ψ, hnorm, hfid⟩
    refine ⟨ψ, hnorm, fun a b hab => ?_⟩
    have heq : ((1 : ℕ) + 1 : ℝ) = (1 + 1 : ℝ) := by norm_num
    rw [heq]
    exact hfid a b hab
  · have hge : 2 ≤ d := by
      have hpos : 0 < d := NeZero.pos d
      omega
    exact WeylHeisenbergSIC.fiducial_d_ge_2 d hge
