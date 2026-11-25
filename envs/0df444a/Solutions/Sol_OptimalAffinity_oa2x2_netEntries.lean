-- Prove2me | solution 1 for OptimalAffinity.oa2x2_netEntries
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:53:55.076219+00:00
-- url     : https://prove2.me/submissions/677474ee-682f-42de-b109-5baebcb3baf1

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution :
    netX oa2x2 0 = -1 ∧ netX oa2x2 1 = 2 ∧
    netY oa2x2 0 = 1 ∧ netY oa2x2 1 = -1 := by
  norm_num [netX, netY, oa2x2]
end OptimalAffinity
