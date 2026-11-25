-- Prove2me | solution 1 for SteerableE2CNN.localized_nonlinearity_equivariant
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-25T12:39:02.57488+00:00
-- url     : https://prove2.me/submissions/b7c16b0b-e176-4140-8da6-710124d4b998

import Mathlib
import Definitions.Def_SteerableE2CNN_Basic
set_option autoImplicit false
open Matrix MeasureTheory
namespace SteerableE2CNN

theorem localized_nonlinearity_equivariant (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρin : MatRep G n) (ρout : MatRep G m) (σ : (n → ℝ) → (m → ℝ))
    (hσ : ∀ (g : G) (v : n → ℝ), σ (repMat ρin g *ᵥ v) = repMat ρout g *ᵥ σ v)
    (t : Plane) (g : G) (f : Plane → n → ℝ) :
    (fun x => σ (indAct G ρin t g f x)) = indAct G ρout t g (fun x => σ (f x)) := by
  funext x
  simp only [indAct, hσ]

end SteerableE2CNN
open SteerableE2CNN in
theorem solution (G : Subgroup O2)
    {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (ρin : MatRep G n) (ρout : MatRep G m) (σ : (n → ℝ) → (m → ℝ))
    (hσ : ∀ (g : G) (v : n → ℝ), σ (repMat ρin g *ᵥ v) = repMat ρout g *ᵥ σ v)
    (t : Plane) (g : G) (f : Plane → n → ℝ) :
    (fun x => σ (indAct G ρin t g f x)) = indAct G ρout t g (fun x => σ (f x)) :=
  localized_nonlinearity_equivariant G ρin ρout σ hσ t g f
