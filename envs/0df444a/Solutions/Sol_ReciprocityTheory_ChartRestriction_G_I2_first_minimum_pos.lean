-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.I2.first_minimum_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T00:54:16.340978+00:00
-- url     : https://prove2.me/submissions/29ed710e-caa3-4b4e-8a57-92a9d231925f

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
theorem _root_.solution (X : PT E) (hne : ∃ x ∈ X.L, x ≠ 0) : 0 < X.la1 := by
  obtain ⟨x0, hx0, hx0ne⟩ := hne
  have hfin : Set.Finite {y : Vsp X.dim | y ∈ X.L ∧ y ≠ 0 ∧ ‖y‖ ≤ ‖x0‖} := by
    apply (ZSpan.setFinite_inter X.b (Metric.isBounded_closedBall (x := (0 : Vsp X.dim))
      (r := ‖x0‖))).subset
    rintro y ⟨hy, -, hyn⟩
    exact ⟨mem_closedBall_zero_iff.2 hyn, hy⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image hfin.toFinset (fun y => ‖y‖)
    ⟨x0, (Set.Finite.mem_toFinset hfin).2 ⟨hx0, hx0ne, le_rfl⟩⟩
  rw [Set.Finite.mem_toFinset] at hm
  obtain ⟨-, hm0, hmle⟩ := hm
  have hpos : 0 < ‖m‖ := norm_pos_iff.2 hm0
  refine lt_of_lt_of_le hpos ?_
  unfold PT.la1
  refine le_csInf ⟨‖x0‖, x0, hx0, hx0ne, rfl⟩ ?_
  rintro t ⟨y, hy, hy0, rfl⟩
  by_cases hyle : ‖y‖ ≤ ‖x0‖
  · exact hmin y ((Set.Finite.mem_toFinset hfin).2 ⟨hy, hy0, hyle⟩)
  · exact le_trans hmle (le_of_lt (not_le.1 hyle))
end ReciprocityTheory.ChartRestriction.G.I2
