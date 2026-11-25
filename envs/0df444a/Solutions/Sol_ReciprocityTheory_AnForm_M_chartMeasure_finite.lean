-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.chartMeasure_finite
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:14:32.209969+00:00
-- url     : https://prove2.me/submissions/9408112b-7b1c-4227-a1b7-687ff8a9252e

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Theorems.Thm_ReciprocityTheory_AnForm_M_chartMeasure_integrable_integral
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Set Filter Topology
open scoped ContDiff ENNReal NNReal
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X] [BorelSpace X]
  [CompactSpace X] [T2Space X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i))
    (j : Fin A.n) : IsFiniteMeasure (chartMeasure A P Φ j) := by
  have hgi : MIntegrable A Φ (fun _ => (1 : ℝ)) := fun k K hKs hK => by
    have := ((locDensCont A Φ hΦ k).mono hKs).integrableOn_compact (μ := volume) hK
    simpa using this
  have hi := (chartMeasure_integrable_integral A P Φ hΦ hPsh j (g := fun _ => (1 : ℝ))
    measurable_const hgi).1
  first
    | exact (integrable_const_iff.1 hi).resolve_left one_ne_zero
    | exact ⟨(integrable_const_iff.1 hi).resolve_left one_ne_zero⟩
end ReciprocityTheory.AnForm.M
