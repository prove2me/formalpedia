-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.height_pow_multiHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:06:03.382117+00:00
-- url     : https://prove2.me/submissions/5a3b3cac-16e5-4a2a-970a-49262cb09486

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationGenericRatioEqRestriction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightProdPowMultiHomogeneous
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_isMultiHomogeneous_mul__1edfc9d4904b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_isMultiHomogeneous_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_height_one_eq_zero
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_gauss_height_additivity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.gpt_zero
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_succ
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.NPB.hImg_zero



set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0
open NumberField ReciprocityTheory.MultiplicativeHeights
namespace ReciprocityTheory.ChartRestriction.G.T0
theorem _root_.solution {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n)
    {g : MvPolynomial (Fin B × Fin n) K} {a : Fin B → ℕ} (hg0 : g ≠ 0)
    (hg : IsMultiHomogeneous a g) (e : ℕ) :
    g ^ e ≠ 0 ∧ IsMultiHomogeneous (e • a) (g ^ e) ∧ h0 (g ^ e) = e * h0 g := by
  induction e with
  | zero => simp [height_one_eq_zero hn, isMultiHomogeneous_one]
  | succ e ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    refine ⟨pow_ne_zero _ hg0, ?_, ?_⟩
    · rw [pow_succ, succ_nsmul]; exact isMultiHomogeneous_mul' h2 hg
    · rw [pow_succ, (ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn h1 hg0 h2 hg).1, h3]
      push_cast; ring
end ReciprocityTheory.ChartRestriction.G.T0
