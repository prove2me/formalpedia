-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_mono__c5aa0228de5f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:56.042235+00:00
-- url     : https://prove2.me/submissions/01ace926-0ab3-4c8b-b28f-7c20617ee0c1

import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_ContDiffFubiniStudyRatioCompChart0
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_HomogeneousLiftHolomorphicOnSnd

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open OnePoint
noncomputable section
variable {e : ℕ} {X : Type*} [TopologicalSpace X]
namespace ReciprocityTheory.AnForm.M
namespace FinHolAtlas.SmoothOn
theorem _root_.solution {A : FinHolAtlas e X} {U V : Set X} {f : X → ℝ}
    (h : A.SmoothOn U f) (hVU : V ⊆ U) : A.SmoothOn V f :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))
end FinHolAtlas.SmoothOn
end ReciprocityTheory.AnForm.M
