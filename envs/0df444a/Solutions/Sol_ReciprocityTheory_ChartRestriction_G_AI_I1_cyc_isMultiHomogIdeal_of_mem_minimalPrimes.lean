-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isMultiHomogIdeal_of_mem_minimalPrimes
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:48:58.874938+00:00
-- url     : https://prove2.me/submissions/fd39e9f5-b2ad-4e68-8ffd-420a43fb4d72

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isWeightedHomogeneous_cycBlockWt
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isHomogeneous_of_isMultiHomogIdeal
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isHomogeneous_of_mem_minimalPrimes
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_cyc_isMultiHomogIdeal_of_isHomogeneous

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
theorem _root_.solution {P W : Ideal (MRingOver R ι)} {s : MRingOver R ι}
    {a : K → ℕ} (hP : IsMultiHomogIdeal P) (hs : IsMultiHomog s a)
    (hW : W ∈ (P ⊔ Ideal.span {s}).minimalPrimes) : IsMultiHomogIdeal W := by
  classical
  refine cyc_isMultiHomogIdeal_of_isHomogeneous fun k => cyc_isHomogeneous_of_mem_minimalPrimes _
    ((cyc_isHomogeneous_of_isMultiHomogIdeal hP k).sup (Ideal.homogeneous_span _ _ ?_)) hW
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_cycBlockWt hs k)⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
