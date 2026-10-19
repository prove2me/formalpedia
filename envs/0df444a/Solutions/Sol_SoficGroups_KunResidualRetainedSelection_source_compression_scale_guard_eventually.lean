-- Prove2me | solution 1 for SoficGroups.KunResidualRetainedSelection.source_compression_scale_guard_eventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.698756+00:00
-- url     : https://prove2.me/submissions/c58e7e7a-30ac-40ee-8168-6a7cc20b575a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedWordPower_RootedIndicatorMarkovModel_IsRootedAtRadius_mono

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunResidualRetainedSelection
open Filter Topology
open scoped BigOperators Pointwise symmDiff
namespace SoficGroups.KunResidualRetainedSelection
theorem _root_.solution
    (H eta : ℕ → ℝ)
    (hH : Tendsto H atTop (𝓝 0))
    (heta : Tendsto eta atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      eta n ≤ (1 : ℝ) / 2 ∧
        2 * (Real.exp (H n) - 1 + 2 * eta n) < 1 := by
  have hhalf : ∀ᶠ n in atTop, eta n ≤ (1 : ℝ) / 2 :=
    (heta.eventually (gt_mem_nhds (by norm_num :
      (0 : ℝ) < (1 : ℝ) / 2))).mono fun _ h => h.le
  have hexp : Tendsto
      (fun n => Real.exp (H n)) atTop (𝓝 1) := by
    simpa only [Function.comp_def, Real.exp_zero] using
      (Real.continuous_exp.tendsto (0 : ℝ)).comp hH
  have hinner : Tendsto
      (fun n => Real.exp (H n) - 1 + 2 * eta n)
      atTop (𝓝 0) := by
    have htwo : Tendsto
        (fun n => (2 : ℝ) * eta n) atTop (𝓝 0) := by
      simpa only [mul_zero] using
        ((tendsto_const_nhds :
          Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul heta)
    have hone : Tendsto
        (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) :=
      tendsto_const_nhds
    simpa only [sub_self, add_zero] using (hexp.sub hone).add htwo
  have hsmallLimit : Tendsto
      (fun n => (2 : ℝ) * (Real.exp (H n) - 1 + 2 * eta n))
      atTop (𝓝 0) := by
    simpa only [mul_zero] using
      ((tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (2 : ℝ)) atTop (𝓝 2)).mul hinner)
  exact hhalf.and
    (hsmallLimit.eventually (gt_mem_nhds zero_lt_one))
end SoficGroups.KunResidualRetainedSelection
