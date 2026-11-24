-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FieldNumbers_PFContracted_isHomogeneous_iff_07f1d1421071
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T01:00:23.998091+00:00
-- url     : https://prove2.me/submissions/b47258b3-dce5-420f-9fec-f0884ca49b49

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContractedDim
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FieldsOfNumbers_PPFContracted

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FieldNumbers
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
open GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {F : Type*} [Field F]
attribute [local instance] MvPolynomial.weightedGradedAlgebra
namespace GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
theorem _root_.solution {M : Type*} [AddCommMonoid M] [DecidableEq M] (w : (Σ k, ι k) → M)
    (I : Ideal (MRing ι F)) :
    I.IsHomogeneous (weightedHomogeneousSubmodule F w) ↔
      ∀ (m : M), ∀ r ∈ I, weightedHomogeneousComponent w m r ∈ I := by
  constructor
  · intro h m r hr
    exact (mem_iff_weightedHomogeneousComponent_mem F w h r).mp hr m
  · intro h m r hr
    have := h m r hr
    rwa [← weightedDecomposition.decompose'_apply] at this
end GroundTheory.Heights₂.Heights.FieldNumbers.PFContracted
