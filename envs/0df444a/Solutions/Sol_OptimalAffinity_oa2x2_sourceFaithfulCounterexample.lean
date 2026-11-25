-- Prove2me | solution 1 for OptimalAffinity.oa2x2_sourceFaithfulCounterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:24.887798+00:00
-- url     : https://prove2.me/submissions/9b3b3d38-7c17-4832-a9a8-02a98d519321

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
theorem _root_.solution :
    ∃ (N : Network) (x y : ℝ),
      SourceValid N ∧ IsUniqueGlobalMaximum N x y ∧
      affinityExp N x y < seedRatio N := by
  exact ⟨oa2x2, 1, 1, oa2x2_isSourceNetwork,
    oa2x2_uniqueGlobalMaximum, oa2x2_affinityViolation⟩
end OptimalAffinity
