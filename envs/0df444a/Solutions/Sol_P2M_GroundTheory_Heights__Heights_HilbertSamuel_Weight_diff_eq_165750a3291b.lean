-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_Weight_diff_eq_165750a3291b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T04:58:02.190819+00:00
-- url     : https://prove2.me/submissions/17ceb911-39c2-4d8a-b56f-87ce2564361d

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_PotentialTheory_IsPotentialOfFun
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_BergmanObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MeasureTheory Set ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M
open scoped ComplexConjugate ENNReal ContDiff
noncomputable section
variable {D : ℕ} {X : Type} [TopologicalSpace X]
open GroundTheory.Heights₂.Heights.HilbertSamuel.Weight
variable {A : FinHolAtlas D X} {L : HolLineBundle A}
namespace GroundTheory.Heights₂.Heights.HilbertSamuel.Weight
theorem _root_.solution (W₁ W₀ : Weight L) (j : Fin A.n) {x : X} (hx : x ∈ (A.chart j).source) :
    diff W₁ W₀ x = W₁.φ j x - W₀.φ j x := by
  have hi : x ∈ (A.chart (chartIdx A x)).source := Classical.choose_spec (A.cover x)
  rw [diff, W₁.compat (chartIdx A x) j x ⟨hi, hx⟩, W₀.compat (chartIdx A x) j x ⟨hi, hx⟩]
  ring
end GroundTheory.Heights₂.Heights.HilbertSamuel.Weight
