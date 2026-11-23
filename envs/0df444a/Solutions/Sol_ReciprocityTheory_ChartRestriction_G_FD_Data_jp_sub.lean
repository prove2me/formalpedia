-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.jp_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:12.326928+00:00
-- url     : https://prove2.me/submissions/2bc9c32d-0a21-453a-b7cf-e82f8c2ba796

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_sub

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open Matrix NumberField
open scoped ComplexOrder ComplexConjugate
open ReciprocityTheory.ChartRestriction.G.FD.Data
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.Data
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (u v : Fin r → ℂ) :
    X.jp x τ (u - v) = X.jp x τ u - X.jp x τ v := by
  show (2 : ℂ) • X.ppos x τ (u - v) - (u - v) =
    ((2 : ℂ) • X.ppos x τ u - u) - ((2 : ℂ) • X.ppos x τ v - v)
  rw [X.ppos_sub, smul_sub]
  abel
end ReciprocityTheory.ChartRestriction.G.FD.Data
