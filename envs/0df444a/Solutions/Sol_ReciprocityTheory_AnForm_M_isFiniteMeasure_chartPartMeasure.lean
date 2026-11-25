-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.isFiniteMeasure_chartPartMeasure
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:53:13.7267+00:00
-- url     : https://prove2.me/submissions/ae045a65-8e6c-45cd-8d1d-69c31b223a9f

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Measure
import Theorems.Thm_ReciprocityTheory_AnForm_M_chart_weight_compact
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDensCont

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
namespace ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
private theorem chiCont (A : FinHolAtlas e X) (P : ChartPartition A) (j : Fin A.n) :
    ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
  have h := ((P.smooth j) j).continuousOn
  rw [Set.preimage_univ, Set.inter_univ] at h
  exact h
end
end ReciprocityTheory.AnForm.M
end

set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open MeasureTheory FinHolAtlas Filter Topology
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] [BorelSpace X]
    (A : FinHolAtlas e X) (P : ChartPartition A) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (s : ℝ) (j : Fin A.n) :
    IsFiniteMeasure (chartPartMeasure A P Φ s j) := by
  obtain ⟨hC, hCT, hz⟩ := chart_weight_compact A P Φ j
  have hw : ContinuousOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target :=
    continuousOn_const.mul ((chiCont A P j).mul (locDensCont A Φ hΦ j))
  have hi : IntegrableOn (fun y => s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))
      (A.chart j).target := by
    refine IntegrableOn.of_forall_diff_eq_zero ((hw.mono hCT).integrableOn_compact hC)
      (A.chart j).open_target.measurableSet ?_
    intro y hy
    simp [hz y hy.1 hy.2]
  unfold chartPartMeasure
  haveI : IsFiniteMeasure ((volume.restrict (A.chart j).target).withDensity fun y =>
      ENNReal.ofReal (s * (P.χ j ((A.chart j).symm y) * locDens A Φ j y))) :=
    isFiniteMeasure_withDensity_ofReal hi.2
  infer_instance
end ReciprocityTheory.AnForm.M
