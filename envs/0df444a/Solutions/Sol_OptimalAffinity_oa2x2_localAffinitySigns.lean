-- Prove2me | solution 1 for OptimalAffinity.oa2x2_localAffinitySigns
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:20.201399+00:00
-- url     : https://prove2.me/submissions/2be5b317-b7d4-4de2-89bf-606579ea98ce

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution :
    1 < forwardFlux oa2x2 0 1 1 / reverseFlux oa2x2 0 1 1 ∧
    1 < forwardFlux oa2x2 1 1 1 / reverseFlux oa2x2 1 1 1 := by
  norm_num [forwardFlux, reverseFlux, oa2x2]
end OptimalAffinity
