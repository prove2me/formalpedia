-- Prove2me | solution 1 for OptimalAffinity.oa2x2_determinant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:53:31.30286+00:00
-- url     : https://prove2.me/submissions/e0beb9af-6524-4ca9-bf67-48d00b66301c

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : determinant oa2x2 = -1 := by
  norm_num [determinant, netX, netY, oa2x2]
end OptimalAffinity
