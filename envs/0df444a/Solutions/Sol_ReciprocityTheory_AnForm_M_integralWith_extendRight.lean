-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.integralWith_extendRight
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:07:39.879018+00:00
-- url     : https://prove2.me/submissions/47c475a3-6bf8-4f61-ab55-1b592df7e477

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialPullbackStatement
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_LocDens
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IntegrableOnTargetOfTsupport
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_Partition
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_AtlasIndep
import Theorems.Thm_ReciprocityTheory_AnForm_M_locDens_unionAtlas_natAdd

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
    (h : A.Compatible B) (Q : ChartPartition B) (Φ : Fin e → LocPot X) (g : X → ℝ) :
    integralWith (unionAtlas A B h) (Q.extendRight h) Φ g = integralWith B Q Φ g := by
  unfold integralWith
  show ∑ j : Fin (A.n + B.n), _ = _
  rw [Fin.sum_univ_add]
  simp [ChartPartition.extendRight, Fin.append_left, Fin.append_right, locDens_unionAtlas_natAdd]
end ReciprocityTheory.AnForm.M
