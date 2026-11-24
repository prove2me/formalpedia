-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isMultiHomogIdeal_of_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:14:00.744799+00:00
-- url     : https://prove2.me/submissions/1317fb87-2685-45c3-9e02-ddee9af0e7f4

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_exists_blockComponent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution [DecidableEq K] {W : Ideal (MRing ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k))) :
    IsMultiHomogIdeal W := by
  refine ⟨{f | f ∈ W ∧ ∃ a, IsMultiHomog f a}, fun f hf => hf.2, le_antisymm (fun f hf => ?_)
    (Ideal.span_le.mpr fun f hf => hf.1)⟩
  choose g hgW hg using fun a : K → ℕ => exists_blockComponent hW a Finset.univ hf
  have hsum : f = ∑ a ∈ f.support.image (fun m k => ∑ i, m ⟨k, i⟩), g a := by
    ext m
    rw [coeff_sum]
    have e : ∀ a : K → ℕ,
        coeff m (g a) = if (fun k => ∑ i, m ⟨k, i⟩) = a then coeff m f else 0 := by
      intro a
      rw [hg a]
      by_cases h : (fun k => ∑ i, m ⟨k, i⟩) = a
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        exact h (funext fun k => h' k (Finset.mem_univ k))
    simp_rw [e]
    rw [Finset.sum_ite_eq]
    split_ifs with hm
    · rfl
    · by_contra hne
      exact hm (Finset.mem_image_of_mem _ (mem_support_iff.mpr hne))
  rw [hsum]
  refine Ideal.sum_mem _ fun a _ => Ideal.subset_span ⟨hgW a, a, fun m hm k => ?_⟩
  rw [mem_support_iff, hg a] at hm
  by_contra hk
  exact hm (if_neg fun h => hk (h k (Finset.mem_univ k)))
end ReciprocityTheory.ChartRestriction.G.Geo
