-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.Data.Hf_iso_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T13:41:30.885277+00:00
-- url     : https://prove2.me/submissions/66382a0a-2592-4587-9ec5-abe70ca5fde1

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_IsIntegralCc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_FundamentalDomainPointBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_quad_re_pos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_gramPos_posDef
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_hermC_ppos_self
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_Hf_eq_two_ppos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_neg_of_perp

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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) {e : Fin r → ℂ} (he : e ≠ 0)
    (hiso : hermC τ.1 X.Gm e e = 0) : 0 < (X.Hf x τ e e).re := by
  have hA := (X.gramPos_posDef hx τ).inv
  have hHf : X.Hf x τ e e = 2 * hermC τ.1 X.Gm (X.ppos x τ e) e := by
    rw [X.Hf_eq_two_ppos, hiso, sub_zero]
  rw [hHf, X.hermC_ppos_self]
  have hc0 : (fun a => hermC τ.1 X.Gm e (X.colP x τ a)) ≠ 0 := by
    intro h0
    have h3 := X.neg_of_perp hx τ he (fun b => congrFun h0 b)
    rw [hiso] at h3
    simp at h3
  have key := quad_re_pos hA hc0
  rw [show ∀ z : ℂ, (2 * z).re = 2 * z.re from fun z => by simp [Complex.mul_re]]
  exact mul_pos two_pos key
end ReciprocityTheory.ChartRestriction.G.FD.Data
