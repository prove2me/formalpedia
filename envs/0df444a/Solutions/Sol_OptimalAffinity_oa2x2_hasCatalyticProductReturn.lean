-- Prove2me | solution 1 for OptimalAffinity.oa2x2_hasCatalyticProductReturn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:54:44.558084+00:00
-- url     : https://prove2.me/submissions/a7748b2d-a0be-4a7c-af0c-3d9919039463

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : HasCatalyticReaction oa2x2 := by
  refine ⟨1, ?_⟩
  norm_num [HasCatalyticReaction, oa2x2]
end OptimalAffinity
