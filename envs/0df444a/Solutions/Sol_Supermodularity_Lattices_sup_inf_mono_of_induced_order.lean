-- Prove2me | solution 1 for Supermodularity.Lattices.sup_inf_mono_of_induced_order
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T03:57:23.598518+00:00
-- url     : https://prove2.me/submissions/f5c40f7b-ebff-4d44-ac77-5b964020206f

import Mathlib
import Definitions.Def_Supermodularity_Lattices_InducedSetOrder

set_option autoImplicit false

open Supermodularity.Lattices in
theorem solution {X : Type*} [Lattice X] {X' X'' : Set X}
    (hX' : X'.Nonempty) (hX'' : X''.Nonempty) (hle : InducedSetOrder X' X'') :
    (∀ ⦃s : X⦄, IsLUB X' s → ∀ ⦃s' : X⦄, IsLUB X'' s' → s ≤ s') ∧
      (∀ ⦃i : X⦄, IsGLB X' i → ∀ ⦃i' : X⦄, IsGLB X'' i' → i ≤ i') := by
  refine ⟨fun s hs s' hs' => ?_, fun i hi i' hi' => ?_⟩
  · obtain ⟨b, hb⟩ := hX''
    refine hs.2 (fun a ha => ?_)
    exact le_trans le_sup_left (hs'.1 (hle ha hb).2)
  · obtain ⟨a, ha⟩ := hX'
    refine hi'.2 (fun b hb => ?_)
    exact le_trans (hi.1 (hle ha hb).1) inf_le_right
