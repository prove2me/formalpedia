-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AR.Up.MI.isCompact_CmatSet
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:53:25.253516+00:00
-- url     : https://prove2.me/submissions/14f8d79c-7cfc-47c1-b62b-ed1226c2a1fe

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfH
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_IsOrth
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthonormalFlagTranslateHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_OrthogonalFrameDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FourierCoefficientDomain
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArakelovVolumes_UpperBounds_MeasInvStatementPfI
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AR_Up_MI_isClosed_imp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI
open NumberField Matrix MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData ReciprocityTheory.ChartRestriction.G.AR.Inst
open scoped ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.AR.Up.MI
theorem _root_.solution : IsCompact (CmatSet X) := by
  have hS : ∀ a b : Fin r, IsCompact {z : ℂ | (b < a → z = 0) ∧ (a = b → 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2) ∧ (a < b → ‖z‖ ≤ 1)} := by
    intro a b
    apply Metric.isCompact_of_isClosed_isBounded
    · rw [Set.setOf_and, Set.setOf_and]
      refine IsClosed.inter (isClosed_imp (S := {0}) isClosed_singleton)
        (IsClosed.inter (isClosed_imp (S := {z : ℂ | 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2}) ?_) (isClosed_imp (S := {z : ℂ | ‖z‖ ≤ 1}) ?_))
      · exact (isClosed_le continuous_const continuous_norm).inter (isClosed_le continuous_norm continuous_const)
      · exact isClosed_le continuous_norm continuous_const
    · refine (Metric.isBounded_closedBall (x := (0 : ℂ)) (r := 2)).subset ?_
      rintro z ⟨h1, h2, h3⟩
      rw [Metric.mem_closedBall, dist_zero_right]
      rcases lt_trichotomy a b with h | h | h
      · linarith [h3 h]
      · exact (h2 h).2
      · rw [h1 h, norm_zero]
        norm_num
  have e : CmatSet X = Set.pi Set.univ fun τ => Set.pi Set.univ fun a => Set.pi Set.univ fun b =>
      {z : ℂ | (b < a → z = 0) ∧ (a = b → 1 ≤ ‖z‖ ∧ ‖z‖ ≤ 2) ∧ (a < b → ‖z‖ ≤ 1)} := by
    ext β
    simp [CmatSet, Set.mem_pi]
  rw [e]
  exact isCompact_univ_pi fun τ => isCompact_univ_pi fun a => isCompact_univ_pi fun b => hS a b
end ReciprocityTheory.ChartRestriction.G.AR.Up.MI
