-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.nPa_support
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:42:36.576801+00:00
-- url     : https://prove2.me/submissions/17b048c6-892e-4954-a34c-55cf0f7d0eda

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDA
import Definitions.Def_ReciprocityTheory_SemistableReduction_AeBlockSphereEvalNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_Wres_apply
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_norm_by_places
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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) (a : Ω c) (ha : a ≠ 0) :
    {p | p ∈ d.HtOne ∧ d.nPa h c p a ≠ 0}.Finite := by
  have hy : algebraMap (Ω c) (OmS (Ω c) d.D d.N) a ≠ 0 :=
    (map_ne_zero (algebraMap (Ω c) (OmS (Ω c) d.D d.N))).2 ha
  refine ((d.norm_by_places hd h c).2 _ hy).1.subset ?_
  rintro p ⟨hp, hn⟩
  refine ⟨hp, ?_⟩
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finsum_mem_ne_zero hn
  refine ⟨w, hw.1, fun h0 => hw0 ?_⟩
  rw [d.Wres_apply, h0]; simp
end ReciprocityTheory.ChartRestriction.G.T0.Data
