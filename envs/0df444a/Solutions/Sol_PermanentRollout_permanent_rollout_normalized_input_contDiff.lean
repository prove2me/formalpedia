-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_normalized_input_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/668011a6-e66e-4177-980c-e71f3e2f68c4

import Mathlib
import Definitions.Def_Permanent

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k m : ℕ} (j : Fin (k + 1)) :
    ContDiff ℝ 1
      (fun z : permanentRolloutUniformOutputChartDomain k m =>
        permanentRolloutNormalizedInput j z.1) := by
  apply contDiff_pi.2
  intro a
  induction a using Fin.succAboveCases j with
  | x =>
      simp only [permanentRolloutNormalizedInput,
        Fin.insertNth_apply_same]
      fun_prop
  | p q =>
      simp only [permanentRolloutNormalizedInput,
        Fin.insertNth_apply_succAbove]
      fun_prop
end PermanentRollout
