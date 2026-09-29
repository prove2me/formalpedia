-- Prove2me | solution 1 for Supermodularity.Monotonicity.argmax_increasing_of_joint_supermodularity
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T06:46:12.853975+00:00
-- url     : https://prove2.me/submissions/cb785776-0756-4b5b-a431-c336c7b367b6

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn

set_option autoImplicit false

open Supermodularity.Monotonicity in
theorem solution {X T : Type*} [Lattice X] [Lattice T]
    (S : Set (X × T)) (hS : IsSublattice S) (f : X × T → ℝ)
    (hf : SupermodularOn f S) :
    ∀ ⦃t t' : T⦄, t ≤ t' →
      ({x : X | (x, t) ∈ S ∧ ∀ y : X, (y, t) ∈ S → f (y, t) ≤ f (x, t)}).Nonempty →
      ({x : X | (x, t') ∈ S ∧ ∀ y : X, (y, t') ∈ S → f (y, t') ≤ f (x, t')}).Nonempty →
      Supermodularity.Lattices.InducedSetOrder
        {x : X | (x, t) ∈ S ∧ ∀ y : X, (y, t) ∈ S → f (y, t) ≤ f (x, t)}
        {x : X | (x, t') ∈ S ∧ ∀ y : X, (y, t') ∈ S → f (y, t') ≤ f (x, t')} := by
  intro t t' htt' _ _ a ha b hb
  obtain ⟨haS, hamax⟩ := ha
  obtain ⟨hbS, hbmax⟩ := hb
  have hsup : (a, t) ⊔ (b, t') = (a ⊔ b, t') := by
    rw [Prod.mk_sup_mk, sup_of_le_right htt']
  have hinf : (a, t) ⊓ (b, t') = (a ⊓ b, t) := by
    rw [Prod.mk_inf_mk, inf_of_le_left htt']
  have hsupS : (a ⊔ b, t') ∈ S := hsup ▸ hS.supClosed haS hbS
  have hinfS : (a ⊓ b, t) ∈ S := hinf ▸ hS.infClosed haS hbS
  have h1 := hf haS hbS
  rw [hsup, hinf] at h1
  have h2 := hamax (a ⊓ b) hinfS
  have h3 := hbmax (a ⊔ b) hsupS
  refine ⟨⟨hinfS, fun y hy => ?_⟩, ⟨hsupS, fun y hy => ?_⟩⟩
  · have := hamax y hy
    linarith
  · have := hbmax y hy
    linarith
