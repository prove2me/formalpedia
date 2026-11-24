-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.AI.I1.cyc_isHomogeneous_of_isMultiHomogIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:33:49.027617+00:00
-- url     : https://prove2.me/submissions/8d22ccef-f43a-406d-bea5-d6785e98ae35

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_IsFieldIntersection
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppAC
import Definitions.Def_Lemmata_GeneralBFactBis_Imports
import Definitions.Def_Lemmata_FirstBlockLemmaB_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_CycDim
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_AI_I1_isWeightedHomogeneous_cycBlockWt

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
theorem _root_.solution [DecidableEq K] {P : Ideal (MRingOver R ι)}
    (h : IsMultiHomogIdeal P) (k : K) :
    P.IsHomogeneous (weightedHomogeneousSubmodule R (cycBlockWt (ι := ι) k)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx => ?_
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_cycBlockWt ha k)⟩
end ReciprocityTheory.ChartRestriction.G.AI.I1
