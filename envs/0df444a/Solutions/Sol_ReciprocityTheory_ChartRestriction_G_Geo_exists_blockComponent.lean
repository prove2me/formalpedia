-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.exists_blockComponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:10:02.167369+00:00
-- url     : https://prove2.me/submissions/a842a4de-57ac-4768-a23f-b28f6c3600f9

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_weight_blockWeight

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
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k)))
    (a : K → ℕ) (T : Finset K) {f : MRing ι} (hf : f ∈ W) :
    ∃ g ∈ W, ∀ m, coeff m g = if (∀ k ∈ T, ∑ i, m ⟨k, i⟩ = a k) then coeff m f else 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨f, hf, fun m => by simp⟩
  | @insert k T hk ih =>
    obtain ⟨g, hgW, hg⟩ := ih
    refine ⟨weightedHomogeneousComponent (blockWeight k) (a k) g,
      weightedHomogeneousComponent_mem_of_mem ℤ (blockWeight k) (hW k) hgW (a k), fun m => ?_⟩
    rw [coeff_weightedHomogeneousComponent, weight_blockWeight, hg]
    by_cases h1 : ∑ i, m ⟨k, i⟩ = a k <;> by_cases h2 : ∀ k' ∈ T, ∑ i, m ⟨k', i⟩ = a k' <;>
      simp [h1, h2]
end ReciprocityTheory.ChartRestriction.G.Geo
