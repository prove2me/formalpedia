-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors.exists_int_multiple
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:43:27.066869+00:00
-- url     : https://prove2.me/submissions/15b4c604-efb9-46f1-8eef-82406503e813

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_GaussAbsMulSupportFinite
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_HeightTheory_ExistsIntMultiple
import Theorems.Thm_BlockPoly_translEquiv_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_T0_GaussGen_translSEquiv_apply
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
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
open NumberField
open scoped nonZeroDivisors
variable {K : Type} [Field K] [NumberField K]
namespace ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
theorem _root_.solution {κ : Type} (F : MvPolynomial κ K) :
    ∃ (c : K) (G₀ : MvPolynomial κ (𝓞 K)), c ≠ 0 ∧
      MvPolynomial.map (algebraMap (𝓞 K) K) G₀ = MvPolynomial.C c * F := by
  classical
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finset (nonZeroDivisors (𝓞 K))
    (F.support.image fun s => F.coeff s)
  have hy : ∀ s, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = (b : 𝓞 K) • F.coeff s := by
    intro s
    by_cases hs : s ∈ F.support
    · exact RingHom.mem_rangeS.mp (hb _ (Finset.mem_image_of_mem _ hs))
    · have h0 : F.coeff s = 0 := by
        by_contra h
        exact hs (MvPolynomial.mem_support_iff.mpr h)
      exact ⟨0, by rw [map_zero, h0, smul_zero]⟩
  choose y hy using hy
  refine ⟨algebraMap (𝓞 K) K b, ∑ s ∈ F.support, MvPolynomial.monomial s (y s), ?_, ?_⟩
  · exact IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors b.2
  · rw [map_sum]
    simp only [MvPolynomial.map_monomial, hy]
    conv_rhs => rw [MvPolynomial.as_sum F]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [MvPolynomial.C_mul_monomial, Algebra.smul_def]
end ReciprocityTheory.ChartRestriction.G.T0.SatakeVectors
