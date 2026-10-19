-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.zero_support_card_le_half_of_singletons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/7c4d298e-fb6e-4a0e-badb-fe50f3819fcd

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
    2 * (positiveNatSupport
      (fun x => if f x = 0 then 1 else 0)).card ≤
        Fintype.card V := by
  classical
  have hsub :
      positiveNatSupport (fun x => if f x = 0 then 1 else 0) ⊆
        Finset.univ \ singletonSupport f := by
    intro x hx
    have hxpos :=
      (mem_positiveNatSupport
        (fun x => if f x = 0 then 1 else 0) x).mp hx
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
