-- Prove2me | solution 1 for ReciprocityTheory.MultiplicativeHeights.inner_conjVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T15:19:10.299936+00:00
-- url     : https://prove2.me/submissions/f36c4804-28bf-4b7f-a574-cac8f6c617e0

import Definitions.Def_ReciprocityTheory_SemistableReduction_SphereLogIntegrableStatement
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreA
import Definitions.Def_ReciprocityTheory_SemistableReduction_SJCoreB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.MultiplicativeHeights
open MeasureTheory Metric Set Real
namespace ReciprocityTheory.MultiplicativeHeights
theorem _root_.solution {n : ℕ} (c x : EuclideanSpace ℂ (Fin n)) :
    inner ℂ (conjVec c) x = ∑ i, WithLp.ofLp c i * WithLp.ofLp x i := by
  simp [conjVec, PiLp.inner_apply, mul_comm]
end ReciprocityTheory.MultiplicativeHeights
