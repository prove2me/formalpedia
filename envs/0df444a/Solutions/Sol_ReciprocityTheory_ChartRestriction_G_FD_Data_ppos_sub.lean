-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.ppos_sub
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T05:48:39.715131+00:00
-- url     : https://prove2.me/submissions/8c53df2c-a537-4ce0-a5e8-ea70e552add9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_eq

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
    X.ppos x τ (u - v) = X.ppos x τ u - X.ppos x τ v := by
  simp only [X.ppos_eq, hermC_sub_left, sub_mul, Finset.sum_sub_distrib, sub_smul]
end ReciprocityTheory.ChartRestriction.G.FD.Data
