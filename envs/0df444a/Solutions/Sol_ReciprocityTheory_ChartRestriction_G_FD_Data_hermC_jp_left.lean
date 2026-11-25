-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.hermC_jp_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:49:43.531507+00:00
-- url     : https://prove2.me/submissions/c34085a2-be81-4891-853c-15b327fd4c9c

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_smul_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_hermC_sub_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_left

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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (u v : Fin r → ℂ) :
    hermC τ.1 X.Gm (X.jp x τ u) v = hermC τ.1 X.Gm u (X.jp x τ v) := by
  show hermC τ.1 X.Gm ((2 : ℂ) • X.ppos x τ u - u) v =
    hermC τ.1 X.Gm u ((2 : ℂ) • X.ppos x τ v - v)
  rw [hermC_sub_left, hermC_smul_left, hermC_sub_right, hermC_smul_right,
    X.hermC_ppos_left hx τ u v, X.hermC_ppos_right hx τ u v]
  rw [map_ofNat]
end ReciprocityTheory.ChartRestriction.G.FD.Data
