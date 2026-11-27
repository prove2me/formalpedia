-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.meanK_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-27T06:13:45.570142+00:00
-- url     : https://prove2.me/submissions/e7de4bcc-42bc-420b-9e86-5cb9821dfbae

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HFour
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogNormNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightGeneratorLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntegralLeOfAeLeAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_CardEmbPos
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_card_emb_pos
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_gpt_zero
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_succ
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_NPB_hImg_zero
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
open NumberField
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (F G H : (K →+* ℂ) → ℝ) (C r : ℝ) (hle : ∀ sg, F sg ≤ G sg + C + r * H sg) :
    meanK F ≤ meanK G + C + r * meanK H := by
  have hc : (0 : ℝ) < Fintype.card (K →+* ℂ) := card_emb_pos
  have hs : (∑ sg, F sg) ≤ (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg := by
    calc (∑ sg, F sg) ≤ ∑ sg, (G sg + C + r * H sg) := Finset.sum_le_sum (fun sg _ => hle sg)
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
          Finset.mul_sum]
  unfold meanK
  rw [div_le_iff₀ hc]
  have e : ((∑ sg, G sg) / (Fintype.card (K →+* ℂ) : ℝ) + C +
      r * ((∑ sg, H sg) / (Fintype.card (K →+* ℂ) : ℝ))) * (Fintype.card (K →+* ℂ) : ℝ) =
      (∑ sg, G sg) + Fintype.card (K →+* ℂ) * C + r * ∑ sg, H sg := by
    field_simp <;> ring
  linarith
end ReciprocityTheory.ChartRestriction.G.T0.Data
