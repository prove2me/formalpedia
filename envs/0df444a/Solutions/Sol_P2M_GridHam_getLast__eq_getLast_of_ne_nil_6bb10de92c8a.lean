-- Prove2me | solution 1 for P2M_GridHam_getLast__eq_getLast_of_ne_nil_6bb10de92c8a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:24:14.589951+00:00
-- url     : https://prove2.me/submissions/36ce5a39-89ac-4b70-b3c6-8b60f1c75a1b

module
public import Definitions.Def_GridHam_Defs
public import Definitions.Def_GridHam_Coloring

set_option autoImplicit true
@[expose] public section
public section
open GridHam
namespace GridHam
theorem _root_.solution :
    ∀ (l : List Coord) (hne : l ≠ []) (x : Coord),
      l.getLast? = some x → l.getLast hne = x := by
  intro l
  induction l with
  | nil => intro hne; exact absurd rfl hne
  | cons a rest ih =>
    intro hne x h
    cases rest with
    | nil =>
      have h1 : ([a] : List Coord).getLast? = some a := rfl
      rw [h1] at h
      injection h with heq
    | cons b rest' =>
      have hgl2 : (a :: b :: rest').getLast? = (b :: rest').getLast? := rfl
      rw [hgl2] at h
      have hgl3 : (a :: b :: rest').getLast hne = (b :: rest').getLast (by simp) := rfl
      rw [hgl3]
      exact ih (by simp) x h
end GridHam
