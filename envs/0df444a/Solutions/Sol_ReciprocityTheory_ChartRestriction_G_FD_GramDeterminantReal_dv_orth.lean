-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal.dv_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:20:52.308272+00:00
-- url     : https://prove2.me/submissions/9acaf591-d25f-43dc-b786-909337638603

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_Signature
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramDeterminantReal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_sub_left
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_pv_orth

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open Complex Matrix
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
variable {n : ℕ} (f : Fin (n + 1) → Fin r → ℂ) (e : Fin r → ℂ)
namespace ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
theorem _root_.solution (hA : IsUnit (gramF τ G f).det)
    (hA' : IsUnit (gramF τ G (fun a : Fin n => f a.castSucc)).det) (d : Fin n) :
    hermC τ G (dv τ G f e) (f d.castSucc) = 0 := by
  unfold dv
  rw [hC_sub_left, pv_orth τ G f e hA d.castSucc, pv_orth τ G _ e hA' d]
  exact sub_self _
end ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
