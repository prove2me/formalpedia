-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.jp_jp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T13:48:47.668087+00:00
-- url     : https://prove2.me/submissions/afd02a29-6955-471f-be15-93bc2571de9b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_smul_eq
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_sub
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_ppos_ppos

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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (v : Fin r → ℂ) :
    X.jp x τ (X.jp x τ v) = v := by
  show (2 : ℂ) • X.ppos x τ ((2 : ℂ) • X.ppos x τ v - v) - ((2 : ℂ) • X.ppos x τ v - v) = v
  rw [X.ppos_sub, X.ppos_smul_eq, X.ppos_ppos hx]
  have h : (2 : ℂ) • X.ppos x τ v - X.ppos x τ v = X.ppos x τ v := by
    rw [two_smul]
    abel
  rw [h]
  abel
end ReciprocityTheory.ChartRestriction.G.FD.Data
