-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.excess_support_card_le_half_of_singletons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/5741b719-418c-41fe-8391-4ef83e7c4b55

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V : Type*} [Fintype V] [DecidableEq V]
    (f : V → ℕ)
    (hsingle : Fintype.card V ≤ 2 * (singletonSupport f).card) :
    2 * (positiveNatSupport (fun x => f x - 1)).card ≤
      Fintype.card V := by
  classical
  have hsub :
      positiveNatSupport (fun x => f x - 1) ⊆
        Finset.univ \ singletonSupport f := by
    intro x hx
    have hxpos :=
      (mem_positiveNatSupport (fun x => f x - 1) x).mp hx
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    intro hxone
    have hone := (mem_singletonSupport f x).mp hxone
    simp [hone] at hxpos
  have hcard := Finset.card_le_card hsub
  have hpartition := Finset.card_sdiff_add_card_inter
    (Finset.univ : Finset V) (singletonSupport f)
  have hinter :
      ((Finset.univ : Finset V) ∩ singletonSupport f).card =
        (singletonSupport f).card := by
    simp
  have huniv : (Finset.univ : Finset V).card = Fintype.card V := by
    rfl
  omega
end SoficGroups.KunThomFiberCoarea
