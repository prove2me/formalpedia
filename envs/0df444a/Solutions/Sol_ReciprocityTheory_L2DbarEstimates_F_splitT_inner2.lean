-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.splitT_inner2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T14:14:33.541262+00:00
-- url     : https://prove2.me/submissions/72fb6d4a-453c-4b88-828e-453fe8a22eb8

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_MinimalSolutions_HilbertLemmas
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_SplitTest
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_ae
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_F_splitT_inner

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
theorem _root_.solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (ph : M → ℝ) (hph : Continuous ph) (F G : M → E) (hF : MemLp F 2 (wvol n z ph))
    (hG : MemLp G 2 (wvol n z ph)) :
    ⟪hF.toLp F, hG.toLp G⟫_ℂ = ∫ x, ⟪F x, G x⟫_ℂ * (Real.exp (-ph x) : ℂ) ∂vol n z := by
  rw [splitT_inner ph hph F hF (hG.toLp G)]
  refine integral_congr_ae ?_
  have h1 := splitT_ae (n := n) (z := z) ph hph hG.coeFn_toLp
  filter_upwards [h1] with x hx
  rw [hx]
end ReciprocityTheory.L2DbarEstimates.F
