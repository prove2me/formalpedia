-- Prove2me | solution 1 for OptimalAffinity.optimalAffinity_seedLowerBound_false
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:38.22936+00:00
-- url     : https://prove2.me/submissions/75714d42-feac-4fb9-82f2-494b7ebfa657

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_Main
public import Theorems.Thm_OptimalAffinity_oa2x2_affinityViolation
public import Theorems.Thm_OptimalAffinity_oa2x2_isSourceNetwork
public import Theorems.Thm_OptimalAffinity_oa2x2_uniqueGlobalMaximum


set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : ¬ TwoByTwoSeedLowerBound := by
  intro h
  have hbound := h oa2x2 1 1 oa2x2_isSourceNetwork oa2x2_uniqueGlobalMaximum
  exact (not_le_of_gt oa2x2_affinityViolation) hbound
end OptimalAffinity
