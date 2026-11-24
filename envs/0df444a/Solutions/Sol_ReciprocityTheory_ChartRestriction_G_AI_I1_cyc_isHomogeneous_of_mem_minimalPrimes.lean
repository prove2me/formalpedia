-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:52.930809+00:00
-- url     : https://prove2.me/submissions/a0facc9b-6761-4fda-9f66-84d86b0bf827

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim

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
theorem _root_.solution {A : Type*} [CommRing A] [Algebra R A]
    (𝒜 : ℕ → Submodule R A) [GradedRing 𝒜] {I W : Ideal A} (hI : I.IsHomogeneous 𝒜)
    (hW : W ∈ I.minimalPrimes) : W.IsHomogeneous 𝒜 := by
  have hWp : W.IsPrime := hW.1.1
  have h1 : (W.homogeneousCore 𝒜).toIdeal.IsPrime := hWp.homogeneousCore
  have h2 : I ≤ (W.homogeneousCore 𝒜).toIdeal :=
    hI.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hW.1.2)
  have h3 := hW.2 ⟨h1, h2⟩ (Ideal.toIdeal_homogeneousCore_le _ _)
  have e : (W.homogeneousCore 𝒜).toIdeal = W :=
    le_antisymm (Ideal.toIdeal_homogeneousCore_le _ _) h3
  exact e ▸ (W.homogeneousCore 𝒜).isHomogeneous
end ReciprocityTheory.ChartRestriction.G.AI.I1
