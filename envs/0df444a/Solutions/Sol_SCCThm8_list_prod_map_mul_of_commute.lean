-- Prove2me | solution 1 for SCCThm8.list_prod_map_mul_of_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:58.940909+00:00
-- url     : https://prove2.me/submissions/edc1e53d-eb44-406c-a1f1-461757acf8b6

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Counting

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {G ι : Type*} [Group G] (l : List ι) (a b : ι → G)
    (h : ∀ i j, Commute (a i) (b j)) :
    (l.map fun i => a i * b i).prod = (l.map a).prod * (l.map b).prod := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, ih]
    have hx : Commute (b x) (l.map a).prod :=
      Commute.list_prod_right _ _ (fun y hy => by
        obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
        exact (h j x).symm)
    rw [mul_assoc, ← mul_assoc (b x), hx.eq]
    simp only [mul_assoc]
end SCCThm8
