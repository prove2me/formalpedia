-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_measurable_chartWeight_053ad593250d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T05:11:30.089291+00:00
-- url     : https://prove2.me/submissions/fe19e05c-5f77-4400-853b-2262899c153b

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StatementsCurrent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartObjects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_SegreChartProjObjects
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isOpen_chartLiftDom_f424c0a84590
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_contDiff_chartLift_8692f480c9b0


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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {m : ℕ} (σ : Fin m ≃ ((k : K) → ι k)) (i : (k : K) → ι k)
    {g : ((Σ k, ι k) → ℂ) → ℝ} (hg : IsDegZeroSmooth g) : Measurable (chartWeight σ i g) := by
  classical
  have hc : ContinuousOn (g ∘ chartLift σ i) (chartLiftDom σ i) :=
    hg.1.continuousOn.comp (contDiff_chartLift σ i (n := 0)).continuous.continuousOn fun _ hx => hx
  unfold chartWeight
  exact hc.measurable_piecewise (continuousOn_const (c := (0 : ℝ))) (isOpen_chartLiftDom σ i).measurableSet
end GroundTheory.Heights₂.Heights
