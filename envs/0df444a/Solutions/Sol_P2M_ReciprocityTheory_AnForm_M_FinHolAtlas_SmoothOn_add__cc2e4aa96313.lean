-- Prove2me | solution 1 for P2M_ReciprocityTheory_AnForm_M_FinHolAtlas_SmoothOn_add__cc2e4aa96313
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-27T05:13:52.823134+00:00
-- url     : https://prove2.me/submissions/64eca513-bc95-4269-8f2e-158362e6223c

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
theorem _root_.solution {A : FinHolAtlas e X} {U : Set X} {f g : X → ℝ}
    (hf : A.SmoothOn U f) (hg : A.SmoothOn U g) : A.SmoothOn U (fun x => f x + g x) :=
  fun j => (hf j).add (hg j)
end FinHolAtlas.SmoothOn
end ReciprocityTheory.AnForm.M
