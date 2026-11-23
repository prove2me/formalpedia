-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.chart_weight_compact
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:32:44.268497+00:00
-- url     : https://prove2.me/submissions/048f6111-dbc4-41f0-b72d-0adc25bd6af7

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Measure

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas e X)
    (P : ChartPartition A) (Φ : Fin e → LocPot X) (j : Fin A.n) :
    IsCompact ((A.chart j) '' tsupport (P.χ j)) ∧
      (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target ∧
      ∀ y ∈ (A.chart j).target, y ∉ (A.chart j) '' tsupport (P.χ j) →
        P.χ j ((A.chart j).symm y) = 0 := by
  have hK : IsCompact (tsupport (P.χ j)) := (isClosed_tsupport _).isCompact
  have hsrc := P.tsupport_subset j
  refine ⟨hK.image_of_continuousOn ((A.chart j).continuousOn.mono hsrc), ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (hsrc hx)
  · intro y hy hy'
    apply image_eq_zero_of_notMem_tsupport
    intro h
    exact hy' ⟨_, h, (A.chart j).right_inv hy⟩
end ReciprocityTheory.AnForm.M
