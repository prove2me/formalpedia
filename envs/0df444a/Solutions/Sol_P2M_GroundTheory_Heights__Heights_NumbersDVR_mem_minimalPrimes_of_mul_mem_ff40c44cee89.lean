-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_mem_minimalPrimes_of_mul_mem_ff40c44cee89
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:48:05.088585+00:00
-- url     : https://prove2.me/submissions/b81227a7-e8b4-4460-a7f1-7e39961bf104

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Cartier

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
variable {A : Type*} [CommRing A]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {J J' W : Ideal A} {s t : A} (hs : s ∉ W) (ht : t ∉ W)
    (hsJ : ∀ x ∈ J, s * x ∈ J') (htJ : ∀ x ∈ J', t * x ∈ J) (hW : W ∈ J.minimalPrimes) :
    W ∈ J'.minimalPrimes := by
  have hWp : W.IsPrime := hW.1.1
  refine ⟨⟨hWp, fun x hx => ?_⟩, fun Q hQ hQW => hW.2 ⟨hQ.1, fun x hx => ?_⟩ hQW⟩
  · exact (hWp.mem_or_mem (hW.1.2 (htJ x hx))).resolve_left ht
  · exact (hQ.1.mem_or_mem (hQ.2 (hsJ x hx))).resolve_left (fun h => hs (hQW h))
end GroundTheory.Heights₂.Heights.NumbersDVR
