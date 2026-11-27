-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_HoloOn_sub__eb141925f045
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:51.634805+00:00
-- url     : https://prove2.me/submissions/e8f8196b-4774-4c70-b6b0-a215e7ef8162

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
    (hf : A.HoloOn U f) (hg : A.HoloOn U g) : A.HoloOn U (fun x => f x - g x) :=
  fun j => (hf j).sub (hg j)
end FinHolAtlas.HoloOn
end ReciprocityTheory.AnForm.M
