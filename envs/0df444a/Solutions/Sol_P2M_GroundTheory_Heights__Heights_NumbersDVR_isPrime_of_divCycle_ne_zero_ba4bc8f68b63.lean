-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_isPrime_of_divCycle_ne_zero_ba4bc8f68b63
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:00:40.048807+00:00
-- url     : https://prove2.me/submissions/a5d37af8-1297-4ecc-ab0d-5701612f5c53

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_LocalLengthAdditivityTorsionFree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Statements

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
universe u v
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {K : Type*} {ι : K → Type*} {R : Type*} [CommRing R]
    {P : Ideal (MRing ι R)} {f : MRing ι R} {W : Ideal (MRing ι R)} (h : divCycle P f W ≠ 0) :
    W.IsPrime := by
  unfold divCycle at h
  split_ifs at h with hW
  · exact hW.1.1.1
  · exact absurd rfl h
end GroundTheory.Heights₂.Heights.NumbersDVR
