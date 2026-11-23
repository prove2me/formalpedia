-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds.psgn_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:59.725577+00:00
-- url     : https://prove2.me/submissions/11c60e6e-fa86-4023-8f76-2b6ee5add511

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PosDefOfBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_SignTypeCancelIdentity
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_psgn_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_psgn_eq_one


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open scoped ComplexConjugate ComplexOrder
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
theorem _root_.solution (p0 k : ℕ) : psgn p0 (p0 + k) = (-1) ^ k := by
  induction k with
  | zero => simp [psgn_eq_one le_rfl]
  | succ k ih =>
    rw [← add_assoc, psgn_succ, ih, sgn, if_neg (by omega), pow_succ]
end ReciprocityTheory.ChartRestriction.G.FD.OrthonormalChartBounds
