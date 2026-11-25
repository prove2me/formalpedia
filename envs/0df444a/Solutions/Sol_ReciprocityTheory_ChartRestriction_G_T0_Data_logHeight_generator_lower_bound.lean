-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.Data.logHeight_generator_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:46:46.487443+00:00
-- url     : https://prove2.me/submissions/af2f819e-ce9c-40d4-a5f8-2ccb973f13ad

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_HtDefs
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_UniformizerOfResidueIndep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GoodPrimesProperties
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_NormByPlaces
import Definitions.Def_ReciprocityTheory_SemistableReduction_TorusL2CauchyInequality
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_FsumEqSum
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_LogHeightGeneratorLowerBound
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_h0_zero
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_Data_good_primes_properties
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
import Theorems.Thm_ReciprocityTheory_MultiplicativeHeights_Closed_sphere_height_lower_bound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] BlockPoly.translEquiv_apply
attribute [local simp] ReciprocityTheory.ChartRestriction.G.T0.GaussGen.translSEquiv_apply



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
theorem _root_.solution (hd : d.AxH 𝒜) (h : d.S1) (c : ι) {p : Ideal (KTp K d.D d.N)} (hp : p ∈ d.HtOne)
    (hg : ∃ w, w ∈ d.GoodP c p) :
    -((d.D : ℝ) * d.dg (d.gen p) * (Real.log (d.N + 1 : ℕ) + 1 / 2)) ≤ ReciprocityTheory.MultiplicativeHeights.h0 (d.gen p) := by
  by_cases h0 : d.gen p = 0
  · rw [h0, d.h0_zero]
    have : d.dg 0 = 0 := by simp [dg]
    rw [this]; simp
  · have hm := (d.good_primes_properties hd h c).2.1 p hp hg
    have := ReciprocityTheory.MultiplicativeHeights.Closed.sphere_height_lower_bound K (d.D + 1) (d.N + 1) _ (d.gen p) (Nat.succ_pos _) h0 hm
    rw [Fin.sum_univ_succ] at this
    simp only [Fin.succ_ne_zero, if_false, if_true, Nat.cast_zero, zero_mul, zero_add,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at this
    convert this using 2
    ring
end ReciprocityTheory.ChartRestriction.G.T0.Data
