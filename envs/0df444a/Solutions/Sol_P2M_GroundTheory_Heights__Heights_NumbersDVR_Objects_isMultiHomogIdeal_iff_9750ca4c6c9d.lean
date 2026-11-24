-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiHomogIdeal_iff_9750ca4c6c9d
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:36.116415+00:00
-- url     : https://prove2.me/submissions/541d5ae9-9dfb-42b1-bc69-456b364d328c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsVerticalDivOfIsVerticalDivisorAlt
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_Objects_isMultiHomog_iff_f0c1440da5d0

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.NumbersDVR.Objects
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type*} [∀ k, Fintype (ι k)]
variable {R : Type*} [CommRing R]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.NumbersDVR.Objects
theorem _root_.solution (I : Ideal (MRing ι R)) :
    IsMultiHomogIdeal I ↔ ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomogIdeal I := by
  classical
  constructor
  · intro h
    refine ⟨{x | x ∈ I ∧ ∃ a, ReciprocityTheory.ChartRestriction.G.Geo.IsMultiHomog x a}, fun f hf => hf.2, ?_⟩
    refine le_antisymm (fun f hf => ?_) (Ideal.span_le.mpr fun x hx => hx.1)
    rw [← sum_weightedHomogeneousComponent (blockWeight ι) f,
      finsum_eq_sum _ (weightedHomogeneousComponent_finsupp f)]
    refine Ideal.sum_mem _ fun b _ => Ideal.subset_span ⟨h f hf b, b, ?_⟩
    exact (isMultiHomog_iff _ b).mp (weightedHomogeneousComponent_isWeightedHomogeneous b f)
  · rintro ⟨S, hS, rfl⟩ f hf b
    have hI : (Ideal.span S).IsHomogeneous (weightedHomogeneousSubmodule R (blockWeight ι)) := by
      refine Ideal.homogeneous_span _ _ fun x hx => ?_
      obtain ⟨a, ha⟩ := hS x hx
      exact ⟨a, (mem_weightedHomogeneousSubmodule _ _ _ _).mpr ((isMultiHomog_iff x a).mpr ha)⟩
    exact weightedHomogeneousComponent_mem_of_mem R (blockWeight ι) hI hf b
end GroundTheory.Heights₂.Heights.NumbersDVR.Objects
