-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PshMol.radialBump_support
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T16:02:15.173457+00:00
-- url     : https://prove2.me/submissions/1c1ae816-bbea-4ff9-a2de-4be1282086a0

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_IsPshLocallyIntegrableStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMean

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Metric Set Filter Topology Real
open MeasureTheory Metric Set Filter Topology Real
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PshMol
noncomputable section
namespace ReciprocityTheory.AnForm.A.PshMol
theorem _root_.solution (D : ℕ) : Function.support (g0 D) ⊆ ball 0 1 := by
  intro w hw
  have h : (∑ i, ‖w i‖ ^ 2) ∈ ball (0:ℝ) (1 / 4) := by
    have := b0.support_eq ▸ (show (∑ i, ‖w i‖ ^ 2) ∈ Function.support b0 from hw)
    simpa [b0] using this
  rw [mem_ball, dist_zero_right, Real.norm_eq_abs] at h
  rw [mem_ball, dist_zero_right, pi_norm_lt_iff one_pos]
  intro i
  have h1 : ‖w i‖ ^ 2 ≤ ∑ j, ‖w j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖w j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h2 := le_abs_self (∑ j, ‖w j‖ ^ 2)
  nlinarith [norm_nonneg (w i)]
end ReciprocityTheory.AnForm.A.PshMol
