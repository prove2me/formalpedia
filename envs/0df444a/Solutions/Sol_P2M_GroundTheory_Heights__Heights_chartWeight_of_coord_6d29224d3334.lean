-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chartWeight_of_coord_6d29224d3334
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T06:04:59.765443+00:00
-- url     : https://prove2.me/submissions/9678a1a2-b630-492e-a854-8517c69673cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_chartLiftDom_of_coord_0b0f9f6d4975
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chartWeight_of_mem_97102f18b253

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
    (g : ((Σ k, ι k) → ℂ) → ℝ) {x : Fin m → ℂ} (hx : x (σ.symm i) = 1) :
    chartWeight σ i g x = g (chartLift σ i x) :=
  chartWeight_of_mem g (mem_chartLiftDom_of_coord hx)
end GroundTheory.Heights₂.Heights
