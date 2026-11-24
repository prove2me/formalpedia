-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_exists_component_not_mem_53dbbac47368
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:35:39.135894+00:00
-- url     : https://prove2.me/submissions/118dd04f-e2dc-401a-bece-1f5988551637

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_IsMultiHomogIdealSpanSingleton
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PRepresentative

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
universe u
variable {K : Type*} [DecidableEq K] {ι : K → Type*} {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {H : Ideal (MRing ι R)} {x : MRing ι R} (hx : x ∉ H) :
    ∃ e : K → ℕ, weightedHomogeneousComponent (blockWeight ι) e x ∉ H := by
  by_contra h
  simp only [not_exists, not_not] at h
  apply hx
  rw [← sum_weightedHomogeneousComponent (blockWeight ι) (φ := x),
    finsum_eq_sum _ (weightedHomogeneousComponent_finsupp x)]
  exact H.sum_mem fun e _ => h e
end GroundTheory.Heights₂.Heights.NumbersDVR
