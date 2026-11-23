-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.mInt_zero_fun
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:06.122834+00:00
-- url     : https://prove2.me/submissions/9fcc0503-1352-42c7-9644-ec42d08c688e

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
theorem _root_.solution (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) {g : X → ℝ}
    (hg : ∀ x, g x = 0) : mInt A Φ g = 0 := by
  unfold mInt
  split_ifs
  · simp [integralWith, hg]
  · rfl
end ReciprocityTheory.AnForm.M.PLAux
