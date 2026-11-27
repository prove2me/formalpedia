-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.chartPush_symm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:23:24.169385+00:00
-- url     : https://prove2.me/submissions/804bb1aa-6cd3-4be2-a11a-e52ce2c719bf

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
theorem _root_.solution (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (F : (Fin e → ℂ) → ℝ)
    {y : Fin e → ℂ} (hy : y ∈ ψ.target) : chartPush ψ F (ψ.symm y) = F y := by
  simp [chartPush, Set.indicator_of_mem (ψ.map_target hy), ψ.right_inv hy]
end ReciprocityTheory.AnForm.M.PLAux
