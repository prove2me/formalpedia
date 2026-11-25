-- Prove2me | solution 1 for OptimalAffinity.oa2x2_reactant_invertible
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:04:28.751574+00:00
-- url     : https://prove2.me/submissions/aac987e8-0c75-4ee7-b213-ee6564daa4a0

module
public import Definitions.Def_proofs_OptimalAffinity_Affinity
public import Definitions.Def_proofs_OptimalAffinity_SourceBridge
public import Theorems.Thm_OptimalAffinity_oa2x2_reactantDet

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
noncomputable section
namespace OptimalAffinity
theorem _root_.solution : reactantDet oa2x2 ≠ 0 := by
  rw [oa2x2_reactantDet]
  norm_num
end OptimalAffinity
