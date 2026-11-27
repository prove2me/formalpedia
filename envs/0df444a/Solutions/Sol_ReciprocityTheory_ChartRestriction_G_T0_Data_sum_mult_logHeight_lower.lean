-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.sum_mult_logHeight_lower
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:43:23.199526+00:00
-- url     : https://prove2.me/submissions/1820b666-9c7a-4414-a905-ce98e6baeacd

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDD
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntNsg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightGeneratorLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_IntegralLeOfAeLeAffine
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogNormNonneg
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HHINDE
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_fsum_eq_sum
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_logHeight_generator_lower_bound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_nP_nonneg
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
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights MeasureTheory IsDedekindDomain
variable {K : Type} [Field K] [NumberField K] {ι : Type} [Fintype ι]
  {Ω : ι → Type} [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)]
  {WT : Type} [AddCommGroup WT]
  {A : ι → Type} [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)]
  [∀ c, Algebra (𝓞 K) (A c)]
  {𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)}
open ReciprocityTheory.ChartRestriction.G.T0.Data
variable (d : Data K ι Ω WT A)
namespace ReciprocityTheory.ChartRestriction.G.T0.Data
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (G : WT) (c : ι) (f : A c) (hf : f ∈ 𝒜 c G)
    (hf0 : f ≠ 0) (hord : ∀ v, d.admitted c v → 0 ≤ d.ord c v G f) :
    -((d.D : ℝ) * (((∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne),
        d.nP h c G f p * (d.dg (d.gen p) : ℤ) : ℤ)) : ℝ) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤
      ∑ᶠ (p : Ideal (KTp K d.D d.N)) (_ : p ∈ d.HtOne), (d.nP h c G f p : ℝ) * h0 (d.gen p) := by
  classical
  have hfin := (d.good_primes_properties hd h c).2.2.1 G f hf hf0
  set S := hfin.toFinset
  have mem : ∀ p, p ∈ d.HtOne → d.nP h c G f p ≠ 0 → p ∈ S := fun p hp h1 => by
    simp only [S, Set.Finite.mem_toFinset]; exact ⟨hp, h1⟩
  rw [fsum_eq_sum _ S (fun p => d.nP h c G f p * (d.dg (d.gen p) : ℤ))
      (fun p hp h0 => mem p hp fun e => h0 (by simp [e])),
    fsum_eq_sum _ S (fun p => (d.nP h c G f p : ℝ) * h0 (d.gen p))
      (fun p hp h0 => mem p hp fun e => h0 (by simp [e]))]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  by_cases hp : p ∈ d.HtOne
  · simp only [Set.indicator_of_mem hp]
    by_cases hg : ∃ w, w ∈ d.GoodP c p
    · have hL := d.logHeight_generator_lower_bound hd h c hp hg
      have hn0 : (0 : ℝ) ≤ d.nP h c G f p := by exact_mod_cast d.nP_nonneg hd h c hp G f hord
      push_cast at hL ⊢
      nlinarith [mul_le_mul_of_nonneg_left hL hn0]
    · push_neg at hg
      have hG : d.GoodP c p = ∅ := Set.eq_empty_iff_forall_notMem.mpr hg
      have e2 : d.nP h c G f p = 0 := by unfold nP; rw [hG]; simp
      rw [e2]; simp
  · simp [Set.indicator_of_notMem hp]
end ReciprocityTheory.ChartRestriction.G.T0.Data
