-- Prove2me | solution 1 for OptimalAffinity.oa2x2_logAffinityViolation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T20:58:31.413735+00:00
-- url     : https://prove2.me/submissions/c4f6df1d-5223-4882-a7e3-59114ee88d22

module
public import Definitions.Def_proofs_OptimalAffinity_GlobalMaximum
public import Definitions.Def_proofs_OptimalAffinity_Affinity

set_option autoImplicit true
@[expose] public section
public section
open OptimalAffinity
namespace OptimalAffinity
theorem _root_.solution : Real.log (7 / 4 : ℝ) < Real.log 2 := by
  exact Real.strictMonoOn_log (by norm_num) (by norm_num) (by norm_num)
end OptimalAffinity
