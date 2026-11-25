-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.inhV_relevant
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:46:43.355361+00:00
-- url     : https://prove2.me/submissions/20251f18-f07d-42f3-b086-5dd815ece7c0

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_ExistsUniqueStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_InhDivCycleOfSuppEmpty
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_inhV_X_nmem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)] {F : Type*}
  [Field F]
variable [DecidableEq (Σ k, ι k)]
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution (S : Finset (Σ k, ι k)) (h : ∀ k, ∃ i, (⟨k, i⟩ : Σ k, ι k) ∉ S) :
    IsRelevant (inhV F S) :=
  fun k => let ⟨i, hi⟩ := h k; ⟨i, inhV_X_nmem F S hi⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
