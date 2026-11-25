-- Prove2me | solution 1 for OptimalAffinity.oa2x2_overallReaction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:54:39.447918+00:00
-- url     : https://prove2.me/submissions/1da22bff-de31-488c-982a-83a9dc421fe7

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution :
    alpha oa2x2 = 1 ∧ beta oa2x2 = 2 ∧
    yInput oa2x2 = 2 ∧ yOutput oa2x2 = 2 := by
  norm_num [alpha, beta, yInput, yOutput, oa2x2]
end OptimalAffinity
