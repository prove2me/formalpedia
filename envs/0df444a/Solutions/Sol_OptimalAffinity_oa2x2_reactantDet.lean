-- Prove2me | solution 1 for OptimalAffinity.oa2x2_reactantDet
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:03:35.946464+00:00
-- url     : https://prove2.me/submissions/48c9d17c-184a-4f43-965d-10dcf41b10c2

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section
namespace OptimalAffinity
theorem _root_.solution : reactantDet oa2x2 = 2 := by
  norm_num [reactantDet, oa2x2]
end OptimalAffinity
