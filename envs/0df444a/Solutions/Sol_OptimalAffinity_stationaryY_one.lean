-- Prove2me | solution 1 for OptimalAffinity.stationaryY_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:47.389808+00:00
-- url     : https://prove2.me/submissions/5575539a-daf0-4fea-a8b4-53d01f481acf

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section
namespace OptimalAffinity
theorem _root_.solution : stationaryY 1 = 1 := by
  norm_num [stationaryY]
end OptimalAffinity
