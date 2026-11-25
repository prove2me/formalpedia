-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sgn_dOf_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:02:24.914307+00:00
-- url     : https://prove2.me/submissions/ffaab8bc-049a-4b01-bc6f-c499cc0bd62f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_dOf_real
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_dmin_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_psgn_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_Data_mem_dom_iff


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
open NumberField Complex Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
namespace ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) :
    0 < sgn X.p0 k * (dOf X x τ k).re := by
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 k.castSucc
  have h2 := ((X.mem_dom_iff x).1 hx τ).2 k.succ
  rw [dmin_succ X hx τ k, Complex.mul_re, dOf_real X hx τ k, mul_zero, sub_zero] at h2
  rw [Fin.val_succ, psgn_succ] at h2
  rw [Fin.coe_castSucc] at h1
  by_contra hneg
  push_neg at hneg
  nlinarith
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
