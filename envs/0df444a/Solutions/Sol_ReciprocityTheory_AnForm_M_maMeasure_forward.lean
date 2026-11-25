-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.maMeasure_forward
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:14:36.27666+00:00
-- url     : https://prove2.me/submissions/0210d412-269d-4d70-970e-e735967f08c2

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureA
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_MaMeasureB
import Theorems.Thm_ReciprocityTheory_AnForm_M_maMeasure_eq_sum
import Theorems.Thm_ReciprocityTheory_AnForm_M_mInt_eq_integralWith
import Theorems.Thm_ReciprocityTheory_AnForm_M_chartMeasure_integrable_integral

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
theorem _root_.solution (A : FinHolAtlas e X) (Φ : Fin e → LocPot X)
    (hΦ : ∀ i, IsPotential A (Φ i)) (hPsh : ∀ i, IsPsh A (Φ i)) {g : X → ℝ} (hg : Measurable g)
    (hgi : MIntegrable A Φ g) :
    Integrable g (maMeasure A Φ) ∧ mInt A Φ g = ∫ x, g x ∂maMeasure A Φ := by
  by_cases hne : Nonempty (ChartPartition A)
  · rw [maMeasure_eq_sum A Φ hne, mInt_eq_integralWith A Φ hne]
    have hc := fun j => chartMeasure_integrable_integral A hne.some Φ hΦ hPsh j hg hgi
    refine ⟨integrable_finset_sum_measure.2 fun j _ => (hc j).1, ?_⟩
    rw [integral_finset_sum_measure fun j _ => (hc j).1]
    unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [(hc j).2]
    congr 1
    ext y
    ring
  · have h0 : maMeasure A Φ = 0 := by
      unfold maMeasure
      rw [dif_neg hne]
    have h0' : mInt A Φ g = 0 := by
      unfold mInt
      rw [dif_neg hne]
    rw [h0, h0']
    simp
end ReciprocityTheory.AnForm.M
