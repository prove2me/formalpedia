-- Prove2me | solution 1 for Supermodularity.Monotonicity.argmax_mono_of_strictly_increasing_differences
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T06:48:17.717885+00:00
-- url     : https://prove2.me/submissions/cb521484-6751-4964-96cc-1418cefffdf7

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder
import Definitions.Def_Supermodularity_Monotonicity_SupermodularOn
import Definitions.Def_Supermodularity_Monotonicity_StrictlyIncreasingDifferencesOn

set_option autoImplicit false

open Supermodularity.Monotonicity in
theorem solution {X T : Type*} [Lattice X]
    [PartialOrder T] (S : T → Set X) (f : X → T → ℝ)
    (hS : ∀ ⦃t t' : T⦄, t ≤ t' → Supermodularity.Lattices.InducedSetOrder (S t) (S t'))
    (hsuper : ∀ t : T, SupermodularOn (fun x => f x t) Set.univ)
    (hdiff : StrictlyIncreasingDifferencesOn f Set.univ)
    {t' t'' : T} (ht : t' < t'') {x' x'' : X}
    (hx' : x' ∈ S t' ∧ ∀ y ∈ S t', f y t' ≤ f x' t')
    (hx'' : x'' ∈ S t'' ∧ ∀ y ∈ S t'', f y t'' ≤ f x'' t'') :
    x' ≤ x'' := by
  by_contra hne
  obtain ⟨haS, hamax⟩ := hx'
  obtain ⟨hbS, hbmax⟩ := hx''
  obtain ⟨hinfS, hsupS⟩ := hS ht.le haS hbS
  have hA := hamax (x' ⊓ x'') hinfS
  have hB := hsuper t' (Set.mem_univ x') (Set.mem_univ x'')
  simp only at hB
  have hC := hbmax (x' ⊔ x'') hsupS
  have hlt : x'' < x' ⊔ x'' := by
    refine lt_of_le_of_ne le_sup_right (fun h => hne ?_)
    rw [h]
    exact le_sup_left
  have hD : f x'' t'' - f x'' t' < f (x' ⊔ x'') t'' - f (x' ⊔ x'') t' := by
    have hb' : x'' ∈ ({x : X | (x, t') ∈ (Set.univ : Set (X × T))} ∩
        {x : X | (x, t'') ∈ (Set.univ : Set (X × T))}) := ⟨Set.mem_univ _, Set.mem_univ _⟩
    have hab' : x' ⊔ x'' ∈ ({x : X | (x, t') ∈ (Set.univ : Set (X × T))} ∩
        {x : X | (x, t'') ∈ (Set.univ : Set (X × T))}) := ⟨Set.mem_univ _, Set.mem_univ _⟩
    exact hdiff ht hb' hab' hlt
  linarith
