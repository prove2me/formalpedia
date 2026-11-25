-- Prove2me | solution 1 for OptimalAffinity.oa2x2_optimalAffinityExp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:57:39.225239+00:00
-- url     : https://prove2.me/submissions/525a52c4-7659-4625-b94a-90728d056de8

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : affinityExp oa2x2 1 1 = 7 / 4 := by
  norm_num [affinityExp, forwardFlux, reverseFlux, oa2x2]
end OptimalAffinity
