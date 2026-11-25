-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.G.Geo.qIdeal_isHomogeneous
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T13:12:33.824301+00:00
-- url     : https://prove2.me/submissions/ba85ef1d-52b0-47f9-ac24-a40bea58b558

import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodB
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterGoodF
import Theorems.Thm_ReciprocityTheory_ChartRestriction_G_Geo_isWeightedHomogeneous_qmap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo
open MvPolynomial
noncomputable section
attribute [local instance] MvPolynomial.weightedGradedAlgebra
variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace ReciprocityTheory.ChartRestriction.G.Geo
theorem _root_.solution (P : Ideal (MRing ι)) (hP : IsMultiHomogIdeal P) :
    (qIdeal P).IsHomogeneous (weightedHomogeneousSubmodule ℚ (blkWt (ι := ι))) := by
  obtain ⟨S, hS, rfl⟩ := hP
  rw [qIdeal, Ideal.map_span]
  apply Ideal.homogeneous_span
  rintro _ ⟨f, hf, rfl⟩
  obtain ⟨a, ha⟩ := hS f hf
  exact ⟨_, (mem_weightedHomogeneousSubmodule _ _ _ _).2 (isWeightedHomogeneous_qmap f a ha)⟩
end ReciprocityTheory.ChartRestriction.G.Geo
