-- Prove2me | solution 1 for OptimalAffinity.oa2x2_seedRatio
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:18.291078+00:00
-- url     : https://prove2.me/submissions/9cd1b44a-adb0-44fd-aa08-11b440e7e793

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : seedRatio oa2x2 = 2 := by
  norm_num [seedRatio, alpha, beta, oa2x2]
end OptimalAffinity
