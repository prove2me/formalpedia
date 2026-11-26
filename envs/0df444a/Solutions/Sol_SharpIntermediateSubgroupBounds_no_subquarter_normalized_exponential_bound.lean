-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.no_subquarter_normalized_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:00:03.876001+00:00
-- url     : https://prove2.me/submissions/35da623f-dc0b-4abf-8f1e-616cb1abde30

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_no_vanishing_normalized_bound

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p : ℕ} (hp : 2 ≤ p)
    {α C : ℝ} (hα : α < 1 / 4) :
    ¬ ∀ a : ℕ,
      (p : ℝ)⁻¹ ^ (a * a) * (totalQBinom p (2 * a) : ℝ) ≤
        C * Real.exp
          (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2) := by
  intro hbound
  apply no_vanishing_normalized_bound hp
    (fun a : ℕ ↦ C * Real.exp
      (Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2))
  · have hcast : Tendsto (fun a : ℕ ↦ (a : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hsq : Tendsto (fun a : ℕ ↦ (a : ℝ) ^ 2) atTop atTop := by
      simpa [pow_two] using hcast.atTop_mul_atTop₀ hcast
    have hlog : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < p))
    have hcoef : Real.log (p : ℝ) * (4 * α - 1) < 0 := by
      exact mul_neg_of_pos_of_neg hlog (by linarith)
    have hexponent : Tendsto (fun a : ℕ ↦
        Real.log (p : ℝ) * (4 * α - 1) * (a : ℝ) ^ 2) atTop atBot := by
      simpa [mul_assoc] using hsq.const_mul_atTop_of_neg hcoef
    have hconst : Tendsto (fun _ : ℕ ↦ C) atTop (nhds C) := tendsto_const_nhds
    simpa only [Function.comp_apply, mul_zero] using
      hconst.mul (Real.tendsto_exp_atBot.comp hexponent)
  · exact hbound
end SharpIntermediateSubgroupBounds
