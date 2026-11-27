-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.smooth_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:29.349005+00:00
-- url     : https://prove2.me/submissions/7e94471f-25cb-4391-9430-be4fad7e4134

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PartsSt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HessCEqZeroOfEventuallyEqZero

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.M.PLAux
open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M.PLAux
theorem _root_.solution {A : FinHolAtlas e X} {ι : Type} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, A.Smooth (f i)) : A.Smooth (fun x => ∑ i ∈ s, f i x) := fun j =>
  ContDiffOn.sum fun i hi => hf i hi j
end ReciprocityTheory.AnForm.M.PLAux
