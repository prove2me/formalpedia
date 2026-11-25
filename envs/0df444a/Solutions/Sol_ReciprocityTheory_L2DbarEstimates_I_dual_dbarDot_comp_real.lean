-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.I.dual_dbarDot_comp_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:31:16.985554+00:00
-- url     : https://prove2.me/submissions/ab3bc31e-b52f-4191-9132-afc383a66a7c

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_BergmanExistsStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_TsupportDbSubset
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_AddLogPosOfThreeQuartersLe
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_comp_real
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_db_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.I
open MeasureTheory Metric Filter Topology
open scoped ENNReal ContDiff
universe u
noncomputable section
namespace ReciprocityTheory.L2DbarEstimates.I
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℝ → ℝ)
    (hk : ContDiff ℝ ∞ k) (f : M → ℝ) (hf : CkR n z 1 f) (x : M) (ξ : Fin n → ℂ) :
    ‖dbarDot n z (fun y => (k (f y) : ℂ)) x ξ‖ =
      |deriv k (f x)| * ‖dDot n z (fun y => (f y : ℂ)) x ξ‖ := by
  have : dbarDot n z (fun y => (k (f y) : ℂ)) x ξ =
      ((deriv k (f x) : ℝ) : ℂ) * (starRingEnd ℂ) (dDot n z (fun y => (f y : ℂ)) x ξ) := by
    unfold dbarDot dDot
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [db_comp_real n z k hk f hf i x, db_ofReal, map_mul]
    ring
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_conj]
end ReciprocityTheory.L2DbarEstimates.I
