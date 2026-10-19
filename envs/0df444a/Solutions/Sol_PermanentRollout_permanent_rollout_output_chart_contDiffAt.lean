-- Prove2me | solution 1 for PermanentRollout.permanent_rollout_output_chart_contDiffAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:02.589874+00:00
-- url     : https://prove2.me/submissions/33241e62-e5f1-40cf-aca6-07233c9ca3ef

import Mathlib
import Definitions.Def_Permanent
import Theorems.Thm_PermanentRollout_permanent_rollout_complex_div_contDiffAt
import Theorems.Thm_PermanentRollout_permanent_rollout_normalized_input_contDiff

set_option autoImplicit true
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 100000
open PermanentRollout
open Set Filter Module
open scoped BigOperators ENNReal
noncomputable section
namespace PermanentRollout
theorem _root_.solution
    {k m : ℕ}
    (g : (Fin (k + 1) → ℂ) → (Fin (m + 1) → ℂ))
    (hg : ContDiff ℝ 1 g)
    (j : Fin (k + 1)) (ell : Fin (m + 1))
    (z : permanentRolloutUniformOutputChartDomain k m)
    (hz : g (permanentRolloutNormalizedInput j z.1) ell ≠ 0) :
    ContDiffAt ℝ 1 (permanentRolloutOutputChart g j ell) z := by
  have hnorm := permanent_rollout_normalized_input_contDiff (m := m) j
  have hgrad : ContDiff ℝ 1
      (fun w : permanentRolloutUniformOutputChartDomain k m =>
        g (permanentRolloutNormalizedInput j w.1)) :=
    hg.comp hnorm
  apply contDiffAt_pi.2
  intro r
  apply contDiffAt_pi.2
  intro a
  induction a using Fin.succAboveCases ell with
  | x =>
      simp only [permanentRolloutOutputChart,
        Fin.insertNth_apply_same]
      apply permanent_rollout_complex_div_contDiffAt
      · apply ContDiffAt.neg
        apply ContDiffAt.sum
        intro q _
        apply ContDiffAt.mul
        · fun_prop
        · exact ((contDiff_apply ℝ ℂ (ell.succAbove q)).comp
            hgrad).contDiffAt
      · exact ((contDiff_apply ℝ ℂ ell).comp hgrad).contDiffAt
      · exact hz
  | p q =>
      simp only [permanentRolloutOutputChart,
        Fin.insertNth_apply_succAbove]
      fun_prop
end PermanentRollout
