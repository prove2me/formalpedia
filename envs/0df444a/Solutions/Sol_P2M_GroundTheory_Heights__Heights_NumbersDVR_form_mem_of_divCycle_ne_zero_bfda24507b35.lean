-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_form_mem_of_divCycle_ne_zero_bfda24507b35
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:46:51.944681+00:00
-- url     : https://prove2.me/submissions/f7858ef7-b125-485a-9736-e1fe3ff044c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CutIdentityRightSideCongrOfSubMem
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_LocalizedQuotientIsSimpleModuleOfMul

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
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {x : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P x W ≠ 0) : x ∈ W := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW.1.1.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self x))
  · exact absurd rfl h
end GroundTheory.Heights₂.Heights.NumbersDVR
