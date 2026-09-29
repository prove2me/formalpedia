-- Prove2me | solution 1 for Supermodularity.Monotonicity.argmax_increasing_of_increasing_differences
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T06:37:36.068453+00:00
-- url     : https://prove2.me/submissions/44e46231-91cd-44b1-92a0-edb2ae2d2a3e

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Monotonicity_IncreasingDifferencesOn

set_option autoImplicit false

open Supermodularity.Monotonicity in
theorem solution {X T : Type*} [Lattice X] [PartialOrder T]
    (S : T → Set X) (f : X → T → ℝ)
    (hS : ∀ ⦃t t' : T⦄, t ≤ t' → Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (hsuper : ∀ t : T, SupermodularOn (fun x => f x t) Set.univ)
    (hdiff : IncreasingDifferencesOn f Set.univ) :
    ∀ ⦃t t' : T⦄, t ≤ t' →
      ({x : X | x ∈ S t ∧ ∀ y ∈ S t, f y t ≤ f x t}).Nonempty →
      ({x : X | x ∈ S t' ∧ ∀ y ∈ S t', f y t' ≤ f x t'}).Nonempty →
      Supermodularity.Lattices.InducedSetOrder
        {x : X | x ∈ S t ∧ ∀ y ∈ S t, f y t ≤ f x t}
        {x : X | x ∈ S t' ∧ ∀ y ∈ S t', f y t' ≤ f x t'} := by
  intro t t' htt' _ _ a ha b hb
  obtain ⟨haS, hamax⟩ := ha
  obtain ⟨hbS, hbmax⟩ := hb
  obtain ⟨hinfS, hsupS⟩ := hS htt' haS hbS
  -- A := f a t - f (a ⊓ b) t ≥ 0
  have hA := hamax (a ⊓ b) hinfS
  -- supermodularity at t
  have hB := hsuper t (Set.mem_univ a) (Set.mem_univ b)
  simp only at hB
  -- x' maximal at t'
  have hC := hbmax (a ⊔ b) hsupS
  -- increasing differences: f b t' - f b t ≤ f (a ⊔ b) t' - f (a ⊔ b) t
  have hD : f b t' - f b t ≤ f (a ⊔ b) t' - f (a ⊔ b) t := by
    rcases lt_or_eq_of_le htt' with hlt | heq
    · have hmono := hdiff hlt
      have hb' : b ∈ ({x : X | (x, t) ∈ (Set.univ : Set (X × T))} ∩
          {x : X | (x, t') ∈ (Set.univ : Set (X × T))}) := ⟨Set.mem_univ _, Set.mem_univ _⟩
      have hab' : a ⊔ b ∈ ({x : X | (x, t) ∈ (Set.univ : Set (X × T))} ∩
          {x : X | (x, t') ∈ (Set.univ : Set (X × T))}) := ⟨Set.mem_univ _, Set.mem_univ _⟩
      exact hmono hb' hab' le_sup_right
    · subst heq
      simp
  refine ⟨⟨hinfS, fun y hy => ?_⟩, ⟨hsupS, fun y hy => ?_⟩⟩
  · have := hamax y hy
    linarith
  · have := hbmax y hy
    linarith
