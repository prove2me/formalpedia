-- Prove2me | solution 1 for SimpleGraph.HomogeneousBlocks.quotient_adj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:13.204108+00:00
-- url     : https://prove2.me/submissions/a5e69c0a-06fa-47ad-a330-9965485fae77

module
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Definitions.Def_RamseyReservoir_Reservoir
public import Definitions.Def_RamseyReservoir_HomogeneousBlocks
public import Theorems.Thm_SimpleGraph_RamseyBound_symm


set_option autoImplicit true
@[expose] public section
public section
open Finset Function
open SimpleGraph
variable {V ι : Type*}
open SimpleGraph.HomogeneousBlocks
variable {G : SimpleGraph V} (F : G.HomogeneousBlocks ι)
namespace SimpleGraph.HomogeneousBlocks
theorem _root_.solution {i j : ι} :
    F.quotient.Adj i j ↔ i ≠ j ∧ ∀ x ∈ F.block i, ∀ y ∈ F.block j, G.Adj x y := by
  rw [quotient, fromRel_adj]
  exact and_congr_right fun _ => or_iff_left_of_imp fun h x hx y hy => (h y hy x hx).symm
end SimpleGraph.HomogeneousBlocks
