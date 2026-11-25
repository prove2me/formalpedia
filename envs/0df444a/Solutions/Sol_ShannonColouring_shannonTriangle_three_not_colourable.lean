-- Prove2me | solution 1 for ShannonColouring.shannonTriangle_three_not_colourable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T16:01:17.285426+00:00
-- url     : https://prove2.me/submissions/4ba94d14-c8a0-4eae-975b-b260e7c475aa

module
public import Definitions.Def_ShannonColouring_Shannon
public import Definitions.Def_ShannonColouring_Sharp
public import Definitions.Def_ShannonColouring_Sanity
public import Theorems.Thm_ShannonColouring_shannonTriangle_not_colourable


set_option autoImplicit true
@[expose] public section
public section
open ShannonColouring
namespace ShannonColouring
theorem _root_.solution :
    ¬ ∃ c : ShannonTriangleEdge 3 → Fin 3, IsProperEdgeColouring (shannonTriangle 3) c :=
  shannonTriangle_not_colourable 3 3 (by norm_num)
end ShannonColouring
