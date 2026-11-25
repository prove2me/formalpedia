-- Prove2me | solution 1 for OptimalAffinity.stationaryY_continuous
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:11.061974+00:00
-- url     : https://prove2.me/submissions/6f144010-ee5c-49b7-8003-709b202ccbe1

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section
namespace OptimalAffinity
theorem _root_.solution : Continuous stationaryY := by
  unfold stationaryY
  fun_prop
end OptimalAffinity
