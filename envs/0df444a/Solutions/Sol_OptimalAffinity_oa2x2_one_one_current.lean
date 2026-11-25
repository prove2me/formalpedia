-- Prove2me | solution 1 for OptimalAffinity.oa2x2_one_one_current
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:29.311126+00:00
-- url     : https://prove2.me/submissions/afaca5e7-3fec-4104-9fc8-53b3fc3ef4b9

module
public import Definitions.Def_proofs_OptimalAffinity_Source
public import Definitions.Def_proofs_OptimalAffinity_Steady
public import Theorems.Thm_OptimalAffinity_oa2x2_current_formula

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : productionCurrent oa2x2 1 1 = 1 := by
  rw [oa2x2_current_formula]
  norm_num
end OptimalAffinity
