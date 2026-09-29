-- Prove2me | solution 1 for Supermodularity.Monotonicity.argmax_isSublattice_of_supermodular
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T23:40:30.470782+00:00
-- url     : https://prove2.me/submissions/721adeac-fa09-449c-a466-288af2102e79

import Mathlib
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

open Supermodularity.Monotonicity

theorem solution {X : Type*} [Lattice X] (f : X → ℝ)
    (hf : SupermodularOn f Set.univ) :
    IsSublattice {x : X | ∀ y : X, f y ≤ f x} := by
  constructor
  · intro x hx y hy z
    have hsm := hf (Set.mem_univ x) (Set.mem_univ y)
    have h1 : f (x ⊔ y) ≤ f x := hx _
    have h2 : f (x ⊓ y) ≤ f x := hx _
    have h4 : f y ≤ f x := hx y
    have h5 : f x ≤ f y := hy x
    have h6 : f z ≤ f x := hx z
    linarith
  · intro x hx y hy z
    have hsm := hf (Set.mem_univ x) (Set.mem_univ y)
    have h1 : f (x ⊔ y) ≤ f x := hx _
    have h2 : f (x ⊓ y) ≤ f x := hx _
    have h4 : f y ≤ f x := hx y
    have h5 : f x ≤ f y := hy x
    have h6 : f z ≤ f x := hx z
    linarith
