-- Prove2me | solution 1 for ReciprocityTheory.AnForm.M.integrableOn_target_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:24:43.551005+00:00
-- url     : https://prove2.me/submissions/b97c9046-84f0-422b-87d0-78728f3a47db

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
theorem _root_.solution {e : ℕ} {X : Type} [TopologicalSpace X]
    (ch : OpenPartialHomeomorph X (Fin e → ℂ)) {Z : Set X} {G : (Fin e → ℂ) → ℝ}
    (hG0 : ∀ y ∈ ch.target, ch.symm y ∉ Z → G y = 0) (hG : IntegrableOn G (ch '' Z)) :
    IntegrableOn G ch.target :=
  hG.of_forall_diff_eq_zero ch.open_target.measurableSet
    (fun y hy => hG0 y hy.1 (fun hz => hy.2 ⟨_, hz, ch.right_inv hy.1⟩))
end ReciprocityTheory.AnForm.M
