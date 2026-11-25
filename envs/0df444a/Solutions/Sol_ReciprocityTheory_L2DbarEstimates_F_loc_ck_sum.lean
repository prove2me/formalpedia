-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.F.loc_ck_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T14:36:21.86419+00:00
-- url     : https://prove2.me/submissions/8c6bdcf9-ae71-4730-8103-d4d780d16675

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_UnweightBackStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_ChartDerivatives_Imports
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_Localization_LocalizeA

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
namespace ReciprocityTheory.L2DbarEstimates.F
theorem _root_.solution {M : Type*} [TopologicalSpace M] (n : ℕ) (z : M → V n) (k : ℕ) {ι : Type*}
    (s : Finset ι) (f : ι → M → ℂ) (hf : ∀ i, Ck n z k (f i)) :
    Ck n z k (fun x => ∑ i ∈ s, f i x) := by
  unfold Ck at hf ⊢
  intro e he
  exact (ContDiffOn.sum fun i _ => hf i e he :
    ContDiffOn ℝ _ (fun y => ∑ i ∈ s, (f i ∘ e.symm) y) e.target)
end ReciprocityTheory.L2DbarEstimates.F
