-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.height_prod_pow_multiHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T06:11:07.817855+00:00
-- url     : https://prove2.me/submissions/9d9b6207-e81e-4019-93fd-192a53d9e7ec

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationGenericRatioEqRestriction
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GeneratorNeZeroOfHeight
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HeightProdPowMultiHomogeneous
import Theorems.Thm_P2M_ReciprocityTheory_ChartRestriction_G_T0_isMultiHomogeneous_mul__1edfc9d4904b
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_isMultiHomogeneous_one
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_height_one_eq_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_height_pow_multiHomogeneous
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
theorem _root_.solution {K : Type} [Field K] [NumberField K] {B n : ℕ} (hn : 0 < n) {ι' : Type*}
    (T : Finset ι') (g : ι' → MvPolynomial (Fin B × Fin n) K) (e : ι' → ℕ)
    (hg : ∀ i ∈ T, g i ≠ 0 ∧ ∃ a, IsMultiHomogeneous a (g i)) :
    (∏ i ∈ T, g i ^ e i) ≠ 0 ∧ (∃ a, IsMultiHomogeneous a (∏ i ∈ T, g i ^ e i)) ∧
      h0 (∏ i ∈ T, g i ^ e i) = ∑ i ∈ T, (e i : ℝ) * h0 (g i) := by
  classical
  induction T using Finset.induction_on with
  | empty => simp [height_one_eq_zero hn]; exact ⟨0, isMultiHomogeneous_one⟩
  | insert q T hq ih =>
    obtain ⟨h1, ⟨a1, h2⟩, h3⟩ := ih fun i hi => hg i (Finset.mem_insert_of_mem hi)
    obtain ⟨hq0, aq, hqa⟩ := hg q (Finset.mem_insert_self q T)
    obtain ⟨p1, p2, p3⟩ := height_pow_multiHomogeneous hn hq0 hqa (e q)
    rw [Finset.prod_insert hq, Finset.sum_insert hq]
    refine ⟨mul_ne_zero p1 h1, ⟨_, isMultiHomogeneous_mul' p2 h2⟩, ?_⟩
    rw [(ReciprocityTheory.MultiplicativeHeights.Closed.gauss_height_additivity K B n _ _ _ _ hn p1 h1 p2 h2).1, p3, h3]
end ReciprocityTheory.ChartRestriction.G.T0
