-- Prove2me | solution 1 for SCCThm8.sum_ind
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:52:07.982974+00:00
-- url     : https://prove2.me/submissions/510871af-b972-48aa-bbe8-6463954f5c90

module
public import Definitions.Def_SCCThm8_Rigidity
public import Definitions.Def_SCCThm8_Counting
public import Definitions.Def_SCCThm8_Degeneration

set_option autoImplicit true
@[expose] public section
public section
open SCCThm8
open Finset
namespace SCCThm8
theorem _root_.solution {n : ℕ} (X : Finset (Fin n)) : ∑ i, ind X i = X.card := by
  unfold ind
  rw [sum_boole]
  simp
end SCCThm8
