-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.jp_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:36.457235+00:00
-- url     : https://prove2.me/submissions/631d05a2-a7ab-4a31-aff6-158d187c1346

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_smul_eq

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
theorem _root_.solution (x : Frame X.Ψ r) (τ : X.Ψ) (k : ℂ) (u : Fin r → ℂ) :
    X.jp x τ (k • u) = k • X.jp x τ u := by
  show (2 : ℂ) • X.ppos x τ (k • u) - k • u = k • ((2 : ℂ) • X.ppos x τ u - u)
  rw [X.ppos_smul_eq, smul_sub, smul_comm k (2 : ℂ)]
end ReciprocityTheory.ChartRestriction.G.FD.Data
