-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FourB_CoverChartLIntegral_analyticAt_chart_d65b277122cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:53:56.151911+00:00
-- url     : https://prove2.me/submissions/a5b42968-c805-451a-bd6c-35d2380f5011

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_StatementsCoverInt
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Degree
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PLCurveA
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LocalDensities_PCoverChartLIntegral

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FourB
open ReciprocityTheory.AnForm.M MeasureTheory Topology
noncomputable section
open GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
theorem _root_.solution {A : FinHolAtlas e X} (j : Fin A.n) {q : X → Fin e → ℂ} {M₀ : Set X}
    (hholo : ∀ i, A.HoloOn M₀ fun x => q x i) {y : Fin e → ℂ}
    (hy : y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' M₀) :
    AnalyticAt ℂ (q ∘ (A.chart j).symm) y :=
  analyticAt_pi_iff.2 fun i => hholo i j y hy
end GroundTheory.Heights₂.Heights.FourB.CoverChartLIntegral
