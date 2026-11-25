-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.neg_aI
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T17:35:27.713743+00:00
-- url     : https://prove2.me/submissions/7fc150d5-3a37-4f2a-ba3e-c7350d286b5f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ValuationResidueLemmas
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDC
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
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights ReciprocityTheory.MultiplicativeHeights.Closed MeasureTheory IsDedekindDomain
  ReciprocityTheory.ChartRestriction.G.T0.HeightMultiplicativity
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (Nr : ∀ c, A c → (Ω c →+* ℂ) → ℝ) (c : ι) (f : A c) (sg : K →+* ℂ)
    (z : BlockSphere d.D (d.N + 1)) :
    ∑ᶠ (P : Ω c →+* ℂ) (_ : P ∈ d.ST c sg (d.tOf z)), -Real.log (Nr c f P) = -d.aI Nr c f sg z := by
  simp only [aI, ← finsum_neg_distrib]
end ReciprocityTheory.ChartRestriction.G.T0.Data
