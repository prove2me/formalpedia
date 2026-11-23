-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds.c_pos
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T11:47:50.476266+00:00
-- url     : https://prove2.me/submissions/b7b9ecce-b7f9-4c40-b1c6-2c9b01488e9c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FlowMinimumLowerBoundHolds
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_TwoSidedBoostBounds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open NumberField Complex MajorantConjugateTransfer FlowMatrixMajorants RankOneBoostIsometries BoostLowerBounds ImaginaryMajorants
open scoped ComplexConjugate
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
open ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
variable {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
theorem _root_.solution (τ : X.Ψ) : 0 < X.c τ := by
  unfold Data.c
  have h : τ.1 X.ξ0 ≠ 0 := (map_ne_zero _).2 X.ξ0_ne
  have := norm_pos_iff.2 h
  linarith
end ReciprocityTheory.ChartRestriction.G.FD.TwoSidedBoostBounds
