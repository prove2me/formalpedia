-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.isHomogeneous_of_isMultiHomogIdeal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:54:04.726648+00:00
-- url     : https://prove2.me/submissions/da0af576-e3a8-40ee-84d0-e342f5f41b83

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSuppA
import Definitions.Def_Lemmata_GeneralBFactTerForm_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isWeightedHomogeneous_of_isMultiHomog

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
theorem _root_.solution [DecidableEq K] {P : Ideal (MRing ι)}
    (h : IsMultiHomogIdeal P) (k : K) :
    P.IsHomogeneous (weightedHomogeneousSubmodule ℤ (blockWeight (ι := ι) k)) := by
  obtain ⟨S, hS, rfl⟩ := h
  refine Ideal.homogeneous_span _ S fun x hx => ?_
  obtain ⟨a, ha⟩ := hS x hx
  exact ⟨a k, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr
    (isWeightedHomogeneous_of_isMultiHomog ha k)⟩
end ReciprocityTheory.ChartRestriction.G.Geo
