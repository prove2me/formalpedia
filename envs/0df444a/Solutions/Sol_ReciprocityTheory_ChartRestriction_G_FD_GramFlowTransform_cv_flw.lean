-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform.cv_flw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:53:51.531614+00:00
-- url     : https://prove2.me/submissions/a19837c8-f83c-4245-950c-4e91246f9f34

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_PositiveMinorUnits
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FundamentalDomains_GramFlowTransform
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hC_add_right
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_FD_GramDeterminantReal_hermC_smul_right


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
open Complex Matrix ReciprocityTheory.ChartRestriction.G.FD.GramDeterminantReal
open scoped ComplexConjugate
noncomputable section
variable {E : Type} [Field E] {r : ℕ} {τ : E →+* ℂ} {G : Matrix (Fin r) (Fin r) E}
namespace ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
theorem _root_.solution (hG : ∀ a b, τ (G b a) = conj (τ (G a b))) (e : Fin r → ℂ)
    (he : hermC τ G e e = 0) (α : ℂ) {n : ℕ} (f : Fin n → Fin r → ℂ) :
    cv τ G (flw α e τ G f) e = cv τ G f e := by
  funext a
  show hermC τ G e (f a + (α * hermC τ G (f a) e) • e) = hermC τ G e (f a)
  rw [GramDeterminantReal.hC_add_right, GramDeterminantReal.hermC_smul_right, he, mul_zero, add_zero]
  all_goals exact hG
end ReciprocityTheory.ChartRestriction.G.FD.GramFlowTransform
