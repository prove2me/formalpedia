-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chartWeight_of_mem_97102f18b253
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:42.385643+00:00
-- url     : https://prove2.me/submissions/90a27b50-f41c-4b13-a222-e36e9953eb45

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo (MRing HermLine IsSmoothHerm pot segre)
open ComplexSets Matrix
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
omit [Fintype K] [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} {σ : Fin m ≃ ((k : K) → ι k)} {i : (k : K) → ι k}
    (g : ((Σ k, ι k) → ℂ) → ℝ) {x : Fin m → ℂ} (hx : x ∈ chartLiftDom σ i) :
    chartWeight σ i g x = g (chartLift σ i x) := by
  classical
  simp only [chartWeight]
  rw [Set.piecewise_eq_of_mem _ _ _ hx]
  rfl
end GroundTheory.Heights₂.Heights
