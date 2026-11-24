-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomogIdeal_iff_08bad36ad538
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:17:03.233473+00:00
-- url     : https://prove2.me/submissions/250aa1be-d481-408b-a0a8-70329ebb1ce0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_IsIntersectionFamily
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_IsMultiHomogIdealIff
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Bridge_isMultiHomog_iff_c75df70a60fa

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Bridge
open MvPolynomial
noncomputable section
variable {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
variable [DecidableEq K] [∀ k, Fintype (ι k)]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.Bridge
theorem _root_.solution (P : Ideal (NumbersDVR.MRing ι R)) :
    NumbersDVR.IsMultiHomogIdeal P ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal (R := R) P := by
  classical
  constructor
  · intro h
    refine ⟨{g | ∃ f ∈ P, ∃ b, g = weightedHomogeneousComponent (NumbersDVR.blockWeight ι) b f},
      ?_, le_antisymm ?_ ?_⟩
    · rintro g ⟨f, -, b, rfl⟩
      exact ⟨b, (isMultiHomog_iff _ _).mp (weightedHomogeneousComponent_isWeightedHomogeneous b f)⟩
    · intro f hf
      rw [← sum_weightedHomogeneousComponent (NumbersDVR.blockWeight ι) f,
        finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
      exact Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨f, hf, b, rfl⟩
    · rw [Ideal.span_le]
      rintro g ⟨f, hf, b, rfl⟩
      exact h f hf b
  · rintro ⟨S, hS, rfl⟩ f hf b
    have hom : (Ideal.span S).IsHomogeneous
        (weightedHomogeneousSubmodule R (NumbersDVR.blockWeight ι)) := by
      refine Ideal.homogeneous_span _ S fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (isMultiHomog_iff x a).mpr ha⟩
    exact weightedHomogeneousComponent_mem_of_mem (h := hom) (hp := hf) (m := b)
end GroundTheory.Heights₂.Heights.Bridge
