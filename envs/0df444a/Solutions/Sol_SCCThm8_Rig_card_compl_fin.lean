-- Prove2me | solution 1 for SCCThm8.Rig.card_compl_fin
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:48:07.385439+00:00
-- url     : https://prove2.me/submissions/6003377e-042a-4ce2-8fb6-e470d9a4aeca

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
theorem _root_.solution (s : Finset (Fin n)) : sᶜ.card = n - s.card := by
  rw [card_compl, Fintype.card_fin]
end SCCThm8.Rig
