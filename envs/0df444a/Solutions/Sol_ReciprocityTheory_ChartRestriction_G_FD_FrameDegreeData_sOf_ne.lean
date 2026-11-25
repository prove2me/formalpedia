-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.sOf_ne
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T14:20:18.532424+00:00
-- url     : https://prove2.me/submissions/6061fe6c-cd5c-445a-8377-4b562ef20e0b

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_FrameDegreeData_abs_re_pos

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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (k : Fin r) : sOf X x τ k ≠ 0 := by
  unfold sOf
  rw [Ne, Complex.ofReal_eq_zero, inv_eq_zero, Real.sqrt_eq_zero']
  exact not_le.mpr (abs_re_pos X hx τ k)
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
