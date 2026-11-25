-- Prove2me | solution 1 for OptimalAffinity.oa2x2_isSourceNetwork
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:56:37.358514+00:00
-- url     : https://prove2.me/submissions/63f412e3-0fe1-42cc-af1d-0b74122f3662

module
public import Mathlib
public import Definitions.Def_proofs_OptimalAffinity_Source
public import Theorems.Thm_OptimalAffinity_oa2x2_ratesPositive
public import Theorems.Thm_OptimalAffinity_oa2x2_determinant
public import Theorems.Thm_OptimalAffinity_oa2x2_unitProductionMode
public import Theorems.Thm_OptimalAffinity_oa2x2_detailedBalance

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : SourceValid oa2x2 := by
  refine ⟨oa2x2_ratesPositive, ?_, oa2x2_unitProductionMode, ?_, ?_, ?_,
    oa2x2_detailedBalance⟩
  · rw [oa2x2_determinant]
    norm_num
  · norm_num [alpha, oa2x2]
  · norm_num [alpha, beta, oa2x2]
  · norm_num [yInput, yOutput, oa2x2]
end OptimalAffinity
