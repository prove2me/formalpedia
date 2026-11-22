-- Prove2me | solution 1 for RelHom.rank_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:43:37.588576+00:00
-- url     : https://prove2.me/submissions/e602c1d0-913e-421b-a456-e3855565b1b2

module
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Defs
public import Mathlib.SetTheory.Ordinal.Rank
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_NashWilliams_Combinatorics_Front_Rank

set_option autoImplicit true
@[expose] public section
public section
open Set List Ordinal
universe u
noncomputable section
namespace RelHom
theorem _root_.solution {α β : Type u} {r : α → α → Prop} {s : β → β → Prop}
    [IsWellFounded α r] [IsWellFounded β s] (f : r →r s) (a : α) :
    IsWellFounded.rank r a ≤ IsWellFounded.rank s (f a) := by
  refine (IsWellFounded.wf (r := r)).induction a
    (C := fun a => IsWellFounded.rank r a ≤ IsWellFounded.rank s (f a))
    (fun a IH => ?_)
  rw [IsWellFounded.rank_eq r a]
  apply Ordinal.iSup_le
  rintro ⟨b, hb⟩
  calc Order.succ (IsWellFounded.rank r b)
      ≤ Order.succ (IsWellFounded.rank s (f b)) := Order.succ_le_succ (IH b hb)
    _ ≤ IsWellFounded.rank s (f a) := by
        rw [IsWellFounded.rank_eq s (f a)]
        exact Ordinal.le_iSup
          (fun c : {c // s c (f a)} => Order.succ (IsWellFounded.rank s c))
          ⟨f b, f.map_rel hb⟩
end RelHom
