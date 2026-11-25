-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.integralWith_extendLeft
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:07:46.570804+00:00
-- url     : https://prove2.me/submissions/b9ad7956-8f74-4d6e-8aba-d3eb11437b8d

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_unionAtlas_castAdd

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
open scoped ContDiff
noncomputable section
variable {e : ℕ} {X : Type} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
theorem _root_.solution [CompactSpace X] [T2Space X] {A B : FinHolAtlas e X}
    (h : A.Compatible B) (P : ChartPartition A) (Φ : Fin e → LocPot X) (g : X → ℝ) :
    integralWith (unionAtlas A B h) (P.extendLeft h) Φ g = integralWith A P Φ g := by
  unfold integralWith
  show ∑ j : Fin (A.n + B.n), _ = _
  rw [Fin.sum_univ_add]
  simp [ChartPartition.extendLeft, Fin.append_left, Fin.append_right, locDens_unionAtlas_castAdd]
end ReciprocityTheory.AnForm.M
