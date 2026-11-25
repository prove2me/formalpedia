-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.sq_le_Qy_of_le_firstMinimum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T00:53:03.674196+00:00
-- url     : https://prove2.me/submissions/8d52781d-01a8-427b-9ece-4ab290f2ba13

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
theorem _root_.solution (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (hne : x ≠ 0) : X.la1 ≤ ‖x‖ := by
  unfold PT.la1
  apply csInf_le
  · exact ⟨0, fun t ht => by obtain ⟨y, -, -, rfl⟩ := ht; exact norm_nonneg y⟩
  · exact ⟨x, hx, hne, rfl⟩
end ReciprocityTheory.ChartRestriction.G.I2
