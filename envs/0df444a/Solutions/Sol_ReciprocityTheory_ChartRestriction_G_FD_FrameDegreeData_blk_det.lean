-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData.blk_det
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:17:38.031292+00:00
-- url     : https://prove2.me/submissions/e93fdcce-eed6-4328-98a8-7a4429993b9d

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_UMatUpper
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_LminorSubmatrixCastSucc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_ProdCastLESucc
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
theorem _root_.solution {x : Frame X.Ψ r} (hx : x ∈ X.dom) (τ : X.Ψ) (c : Fin r) :
    (blk (gram τ.1 X.Gm (mat x τ)) c).det ≠ 0 := by
  intro h0
  have h1 := ((X.mem_dom_iff x).1 hx τ).2 c.castSucc
  have h2 : dmin X.Gm x τ c.castSucc = 0 := h0
  rw [h2, Complex.zero_re, mul_zero] at h1
  exact lt_irrefl _ h1
end ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
