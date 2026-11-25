-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.pushA_intOn
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:08:17.315413+00:00
-- url     : https://prove2.me/submissions/52c085a6-e306-422e-8429-71e10d154abc

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AnalyticSubsetChartLocal
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_LintegralImageEqLintegralNormSqDetMul
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_PushAFinsumInter

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
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (P : ChartPartition A)
    (Φ : Fin e → LocPot X) (g : X → ℝ) (hg : MIntegrable A Φ g) (j : Fin A.n) :
    IntegrableOn (fun y => P.χ j ((A.chart j).symm y) * g ((A.chart j).symm y) *
      locDens A Φ j y) (A.chart j).target := by
  have hK : IsCompact ((A.chart j) '' tsupport (P.χ j)) :=
    (isClosed_tsupport _).isCompact.image_of_continuousOn
      ((A.chart j).continuousOn.mono (P.tsupport_subset j))
  have hKt : (A.chart j) '' tsupport (P.χ j) ⊆ (A.chart j).target := by
    rintro _ ⟨x, hx, rfl⟩
    exact (A.chart j).map_source (P.tsupport_subset j hx)
  have hcont : ContinuousOn (fun y => P.χ j ((A.chart j).symm y)) (A.chart j).target := by
    have := (P.smooth j j).continuousOn
    simpa [Function.comp_def] using this
  have h1 := (hg j _ hKt hK).continuousOn_mul (hcont.mono hKt) hK
  simp_rw [mul_assoc]
  refine h1.of_forall_sdiff_eq_zero (A.chart j).open_target.measurableSet ?_
  rintro y ⟨hy, hyK⟩
  have : P.χ j ((A.chart j).symm y) = 0 := by
    by_contra hne
    exact hyK ⟨_, subset_tsupport _ hne, (A.chart j).right_inv hy⟩
  rw [this, zero_mul]
end ReciprocityTheory.AnForm.M
