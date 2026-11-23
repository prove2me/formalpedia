-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.chartPush_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:42:31.984802+00:00
-- url     : https://prove2.me/submissions/685b83e5-40b3-42e3-8954-e615b79bafd8

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
theorem _root_.solution (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {F : (Fin e → ℂ) → ℝ} {p : X}
    (hp : p ∉ ψ.symm '' tsupport F) : chartPush ψ F p = 0 := by
  unfold chartPush
  by_cases hs : p ∈ ψ.source
  · rw [Set.indicator_of_mem hs]
    by_contra hne
    exact hp ⟨ψ p, subset_tsupport _ hne, ψ.left_inv hs⟩
  · exact Set.indicator_of_notMem hs _
end ReciprocityTheory.AnForm.M.PLAux
