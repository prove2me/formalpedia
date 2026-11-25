-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.exists_short
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T00:55:29.501881+00:00
-- url     : https://prove2.me/submissions/35cb72c7-8181-47ba-ad05-104915dd7197

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_ExistsMaximal
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_SquareIntegrability_SplitC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.I2
open NumberField Complex
open scoped InnerProductSpace
noncomputable section
variable {E : Type} [Field E] [NumberField E]
namespace ReciprocityTheory.ChartRestriction.G.I2
theorem _root_.solution (X : PT E) (hne : ∃ x ∈ X.L, x ≠ 0) {t : ℝ} (h : X.la1 < t) :
    ∃ x ∈ X.L, x ≠ 0 ∧ ‖x‖ < t := by
  unfold PT.la1 at h
  obtain ⟨x, hx, hne'⟩ := hne
  obtain ⟨s, ⟨y, hy, hy0, rfl⟩, hs⟩ := exists_lt_of_csInf_lt (s := {t : ℝ | ∃ x ∈ X.L, x ≠ 0 ∧ t = ‖x‖}) ⟨‖x‖, x, hx, hne', rfl⟩ h
  exact ⟨y, hy, hy0, hs⟩
end ReciprocityTheory.ChartRestriction.G.I2
