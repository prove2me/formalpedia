-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mono__f34c95b6c065
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:15:13.744051+00:00
-- url     : https://prove2.me/submissions/c53c0241-7e38-4e3e-a56a-15dc5bf2fa60

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
namespace FinHolAtlas.HoloOn
theorem _root_.solution {A : FinHolAtlas e X} {U V : Set X} {g : X → ℂ}
    (h : A.HoloOn U g) (hVU : V ⊆ U) : A.HoloOn V g :=
  fun j => (h j).mono (Set.inter_subset_inter_right _ (Set.preimage_mono hVU))
end FinHolAtlas.HoloOn
end ReciprocityTheory.AnForm.M
