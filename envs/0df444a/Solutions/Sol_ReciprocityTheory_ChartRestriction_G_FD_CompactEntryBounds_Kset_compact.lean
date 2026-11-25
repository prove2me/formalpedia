-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds.Kset_compact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:38:38.240335+00:00
-- url     : https://prove2.me/submissions/97bffa78-2ca7-4988-a594-1baa9979a795

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IntegralBasisReduction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_CompactEntryBounds
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_FD_CompactEntryBounds_cont_gram__06583ee5c83d

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
open Matrix NumberField Complex
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
theorem _root_.solution (R : ℝ) : IsCompact (Kset X R) := by
  have hcl : IsClosed (Kset X R) := by
    have : Kset X R = ⋂ τ : X.Ψ, ({w : Frame X.Ψ r | gram τ.1 X.Gm (mat w τ) =
        diagonal (fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ))} ∩
        ⋂ a, ⋂ c, {w : Frame X.Ψ r | ‖w τ a c‖ ≤ R}) := by
      ext w
      simp only [Kset, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_inter_iff]
    rw [this]
    refine isClosed_iInter fun τ => (isClosed_eq (cont_gram' X τ) continuous_const).inter
      (isClosed_iInter fun a => isClosed_iInter fun c => isClosed_le (by fun_prop) continuous_const)
  refine Metric.isCompact_of_isClosed_isBounded hcl ?_
  refine (Metric.isBounded_closedBall (x := (0 : Frame X.Ψ r)) (r := max R 0)).subset ?_
  intro w hw
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun τ =>
    (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun a =>
      (pi_norm_le_iff_of_nonneg (le_max_right _ _)).2 fun c =>
        ((hw τ).2 a c).trans (le_max_left _ _)
end ReciprocityTheory.ChartRestriction.G.FD.CompactEntryBounds
