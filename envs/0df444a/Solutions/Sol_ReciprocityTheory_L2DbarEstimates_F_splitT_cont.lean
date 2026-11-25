-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.splitT_cont
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:30.902081+00:00
-- url     : https://prove2.me/submissions/b4274bee-a0ca-489a-8be8-bfffbd0b3760

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_CkR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Ck_continuous
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_SmoothR_comp
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_Smooth_continuous


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
theorem _root_.solution (f : M → V n) (h : ∀ j, Continuous fun x => f x j) : Continuous f := by
  first
  | exact (PiLp.continuous_toLp 2 _).comp (continuous_pi h)
  | exact (EuclideanSpace.equiv (Fin n) ℂ).symm.continuous.comp (continuous_pi h)
  | exact continuous_induced_rng.2 (continuous_pi h)
end ReciprocityTheory.L2DbarEstimates.F
