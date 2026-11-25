-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.maMeasure_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:19:53.338328+00:00
-- url     : https://prove2.me/submissions/01401411-f26a-4b4f-bfc4-6149cbd9e6cd

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB

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
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X] [MeasurableSpace X]
    (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) (hne : Nonempty (ChartPartition A)) :
    maMeasure A Φ = ∑ j, chartMeasure A hne.some Φ j := by
  unfold maMeasure
  rw [dif_pos hne]
  rfl
end ReciprocityTheory.AnForm.M
