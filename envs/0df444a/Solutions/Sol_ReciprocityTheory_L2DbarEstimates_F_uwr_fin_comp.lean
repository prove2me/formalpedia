-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.uwr_fin_comp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:17:08.262893+00:00
-- url     : https://prove2.me/submissions/d92c94f6-5263-498c-b18b-079e633b4cb2

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightRel
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_ofReal


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.F
open MeasureTheory Filter Topology Set
open scoped ENNReal InnerProductSpace ComplexConjugate ContDiff
noncomputable section
variable {M : Type*} [TopologicalSpace M] [T2Space M] [SecondCountableTopology M]
  [MeasurableSpace M] [BorelSpace M] {n : ℕ} {z : M → V n}
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution (f : M → V n) (p : M → ℝ) (hf : nV n z f p < ⊤) (k : Fin n) :
    ∫⁻ x, ENNReal.ofReal (‖f x k‖ ^ 2 * Real.exp (-p x)) ∂vol n z < ⊤ := by
  unfold nV at hf
  refine lt_of_le_of_lt (lintegral_mono fun x => ?_) hf
  have hk : ‖(f x) k‖ ^ 2 ≤ ‖f x‖ ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
    exact Finset.single_le_sum (f := fun i => ‖(f x) i‖ ^ 2) (fun _ _ => by positivity)
      (Finset.mem_univ k)
  exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right hk (Real.exp_pos _).le)
end ReciprocityTheory.L2DbarEstimates.F
