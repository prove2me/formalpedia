-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.PLAux.analyticAt_compat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:57:23.704835+00:00
-- url     : https://prove2.me/submissions/2e61b7a2-2228-464c-ab2b-f43f519f1557

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
theorem _root_.solution {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) (a : Fin A.n) {p : X} (hpa : p ∈ (A.chart a).source)
    (hpψ : p ∈ ψ.source) : AnalyticAt ℂ (ψ ∘ (A.chart a).symm) (A.chart a p) :=
  (hψ a).1 _ ⟨(A.chart a).map_source hpa, by simpa [(A.chart a).left_inv hpa] using hpψ⟩
end ReciprocityTheory.AnForm.M.PLAux
