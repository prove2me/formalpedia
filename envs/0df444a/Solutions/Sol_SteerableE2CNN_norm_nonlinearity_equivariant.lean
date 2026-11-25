-- Prove2me | solution 1 for SteerableE2CNN.norm_nonlinearity_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T10:34:53.366745+00:00
-- url     : https://prove2.me/submissions/b97edf8c-0f87-47d9-89e0-566d7cae47b5

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic

set_option autoImplicit false

open Matrix MeasureTheory
namespace SteerableE2CNN

theorem norm_nonlinearity_equivariant (G : Subgroup O2)
    {n : Type*} [Fintype n] [DecidableEq n] (ρ : MatRep G n)
    (hρ : ∀ (g : G) (v : n → ℝ), eNorm (repMat ρ g *ᵥ v) = eNorm v)
    (η : ℝ → ℝ) (g : G) (v : n → ℝ) :
    normNL η (repMat ρ g *ᵥ v) = repMat ρ g *ᵥ normNL η v := by
  unfold normNL
  rw [hρ g v, Matrix.mulVec_smul]

end SteerableE2CNN

open SteerableE2CNN in
theorem solution (G : Subgroup O2)
    {n : Type*} [Fintype n] [DecidableEq n] (ρ : MatRep G n)
    (hρ : ∀ (g : G) (v : n → ℝ), eNorm (repMat ρ g *ᵥ v) = eNorm v)
    (η : ℝ → ℝ) (g : G) (v : n → ℝ) :
    normNL η (repMat ρ g *ᵥ v) = repMat ρ g *ᵥ normNL η v :=
  SteerableE2CNN.norm_nonlinearity_equivariant G ρ hρ η g v
