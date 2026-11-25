-- Prove2me | solution 1 for SimpleGraph.ramseyBound_four_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:36:21.292137+00:00
-- url     : https://prove2.me/submissions/98ee9745-ed0b-4ab9-8a06-9e3f6848c106

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Mathlib.Data.Nat.Choose.Central
public import Mathlib.Combinatorics.SimpleGraph.Circulant
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Theorems.Thm_SimpleGraph_ramseyBound_choose
public import Theorems.Thm_SimpleGraph_RamseyBound_mono


set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} (G : SimpleGraph V)
namespace SimpleGraph
theorem _root_.solution (k : ℕ) : RamseyBound (4 ^ k) (k + 1) (k + 1) :=
  (ramseyBound_choose k k).mono (by rw [← two_mul]; exact Nat.centralBinom_le_four_pow k)
end SimpleGraph
