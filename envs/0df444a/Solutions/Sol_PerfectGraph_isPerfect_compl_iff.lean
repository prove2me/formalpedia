-- Prove2me | solution 1 for PerfectGraph.isPerfect_compl_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T10:50:49.918965+00:00
-- url     : https://prove2.me/submissions/4a9b81b6-e404-4f57-a5e3-dbb964ee9d47

module
public import Mathlib
public import Definitions.Def_PerfectLib_Gasparian
public import Definitions.Def_PerfectLib_Perfect
public import Theorems.Thm_PerfectGraph_isPerfect_iff_card_le
public import Theorems.Thm_PerfectGraph_compl_induce_eq


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open PerfectGraph
variable {V : Type*}
namespace PerfectGraph
theorem _root_.solution [Finite V] (G : SimpleGraph V) : IsPerfect Gᶜ ↔ IsPerfect G := by
  rw [isPerfect_iff_card_le, isPerfect_iff_card_le]
  refine forall_congr' fun S => ?_
  rw [compl_induce_eq, indepNum_compl, cliqueNum_compl, mul_comm]
end PerfectGraph
