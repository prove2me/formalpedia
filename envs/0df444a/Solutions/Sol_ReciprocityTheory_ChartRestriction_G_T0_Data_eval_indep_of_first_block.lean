-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.eval_indep_of_first_block
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:49:08.801602+00:00
-- url     : https://prove2.me/submissions/2d9686b4-f346-44a8-a6dc-b279a102a6f8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightDivMultihomogeneous
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormFactorizationClause
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_SphereMeanSubArchimedean
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
theorem _root_.solution (q : KTp K d.D d.N) (m : Fin (d.D + 1) → ℕ) (hm0 : m 0 = 0)
    (hq : IsMultiHomogeneous m q) (sg : K →+* ℂ) (t0 : Fin (d.N + 1) → ℂ)
    (t : Fin d.D → Fin (d.N + 1) → ℂ) : d.evT sg t0 t q = d.evT sg 0 t q := by
  unfold evT
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro s hs
  congr 1
  apply Finset.prod_congr rfl
  rintro ⟨b, j⟩ _
  have hsum : ∑ j : Fin (d.N + 1), s (0, j) = 0 := by
    rw [hq s hs 0, hm0]
  cases b using Fin.cases with
  | zero =>
    have h0 : s (0, j) = 0 := (Finset.sum_eq_zero_iff.mp hsum) j (Finset.mem_univ _)
    simp [h0]
  | succ i => rfl
end ReciprocityTheory.ChartRestriction.G.T0.Data
