-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_exists_blockComponent
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:29.037704+00:00
-- url     : https://prove2.me/submissions/1dadc75b-fbf5-4db7-a632-908222be6615

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_weight_cycBlockWt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] {R : Type*} [CommRing R]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace ReciprocityTheory.ChartRestriction.G.AI.I1
theorem _root_.solution [DecidableEq K] {W : Ideal (MRingOver R ι)}
    (hW : ∀ k, W.IsHomogeneous (weightedHomogeneousSubmodule R (cycBlockWt (ι := ι) k)))
    (a : K → ℕ) (T : Finset K) {f : MRingOver R ι} (hf : f ∈ W) :
    ∃ g ∈ W, ∀ m, coeff m g = if (∀ k ∈ T, ∑ i, m ⟨k, i⟩ = a k) then coeff m f else 0 := by
  induction T using Finset.induction_on with
  | empty => exact ⟨f, hf, fun m => by simp⟩
  | @insert k T hk ih =>
    obtain ⟨g, hgW, hg⟩ := ih
    refine ⟨weightedHomogeneousComponent (cycBlockWt k) (a k) g,
      weightedHomogeneousComponent_mem_of_mem R (cycBlockWt k) (hW k) hgW (a k), fun m => ?_⟩
    rw [coeff_weightedHomogeneousComponent, weight_cycBlockWt, hg]
    by_cases h1 : ∑ i, m ⟨k, i⟩ = a k <;> by_cases h2 : ∀ k' ∈ T, ∑ i, m ⟨k', i⟩ = a k' <;>
      simp [h1, h2]
end ReciprocityTheory.ChartRestriction.G.AI.I1
