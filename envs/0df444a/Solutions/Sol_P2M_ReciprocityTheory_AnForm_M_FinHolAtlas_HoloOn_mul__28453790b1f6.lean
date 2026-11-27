-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_mul__28453790b1f6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:15:18.485311+00:00
-- url     : https://prove2.me/submissions/9af93a0d-eb35-4b23-84fd-079394da3f10

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
theorem _root_.solution {A : FinHolAtlas e X} {U : Set X} {f g : X → ℂ}
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x * g x) :=
  fun j => (hf j).mul (hg j)
end FinHolAtlas.HoloOn
end ReciprocityTheory.AnForm.M
