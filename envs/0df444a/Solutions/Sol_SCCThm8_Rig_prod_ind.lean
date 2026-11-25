-- Prove2me | solution 1 for SCCThm8.Rig.prod_ind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:50:43.16399+00:00
-- url     : https://prove2.me/submissions/1efbd567-238c-4c9b-8fba-7840fc029a18

module
public import Definitions.Def_SCCThm8_Defs
public import Definitions.Def_SCCThm8_Rigidity

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
open SCCThm8.Rig
variable {n : ℕ}
namespace SCCThm8.Rig
theorem _root_.solution {H : Type*} [CommGroup H] (g' : Fin n → H) (S : Finset (Fin n)) :
    ∏ i, g' i ^ (if i ∈ S then (1 : ℤ) else 0) = ∏ i ∈ S, g' i := by
  have := prod_ite_mem univ S g'
  rw [univ_inter] at this
  rw [← this]
  apply prod_congr rfl
  intro i _
  split_ifs <;> simp
end SCCThm8.Rig
