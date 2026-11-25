-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.d4l4_c_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:00:23.348787+00:00
-- url     : https://prove2.me/submissions/eb83576e-eb8e-4a50-a1cc-8322968eb452

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsotropicOutsideLine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowDomainCriterionHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_MajPos
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_HolomorphicPeriodicityExtension

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Complex Filter Topology
variable {E : Type} [Field E] [NumberField E] [NumberField.IsCMField E]
namespace ReciprocityTheory.ChartRestriction.G.FD
theorem _root_.solution {r : ℕ} (X : Data E r) (τ : X.Ψ) : 0 < X.c τ := by
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero τ.1).mpr X.ξ0_ne
  show 0 < 2 * ‖τ.1 X.ξ0‖
  exact mul_pos two_pos (norm_pos_iff.mpr h)
end ReciprocityTheory.ChartRestriction.G.FD
