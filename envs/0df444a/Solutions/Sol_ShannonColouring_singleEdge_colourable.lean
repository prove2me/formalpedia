-- Prove2me | solution 1 for ShannonColouring.singleEdge_colourable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:02:18.907232+00:00
-- url     : https://prove2.me/submissions/7f8dae08-73e1-4436-9a02-1c66d9003a23

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
public import Theorems.Thm_ShannonColouring_singleEdge_degree_le
public import Theorems.Thm_ShannonColouring_shannon


set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution : ∃ c : Unit → Fin 1, IsProperEdgeColouring singleEdge c :=
  shannon singleEdge (fun _ => by simp [singleEdge]) 1 singleEdge_degree_le
end ShannonColouring
