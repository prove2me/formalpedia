-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_PointIdealMultiProj_coneMap_monomial_isWeightedHomogeneous_3f0ae37a1420
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:40:38.889397+00:00
-- url     : https://prove2.me/submissions/2e31d549-c480-4be2-b318-1bc911639c74

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsPointIdealMultiProj
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PPointIdealMultiProj

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
open GroundTheory.Heights₂.Heights.NumbersDVR.PointIdealMultiProj
variable {F : Type*} [Field F] {L : Type*} [Field L] [Algebra F L]
  {K : Type*} [DecidableEq K] {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.PointIdealMultiProj
theorem _root_.solution (z : (Σ k, ι k) → L) (d : (Σ k, ι k) →₀ ℕ) (a : F) :
    IsWeightedHomogeneous (coneWeight K) (pointConeMap F z (monomial d a))
      (Finsupp.weight (blockWeight ι) d) := by
  rw [pointConeMap, aeval_monomial, MvPolynomial.algebraMap_apply, Finsupp.weight_apply, Finsupp.prod,
    Finsupp.sum]
  refine IsWeightedHomogeneous.C_mul ?_ _
  refine IsWeightedHomogeneous.prod _ _ _ fun p _ => ?_
  exact ((isWeightedHomogeneous_X (R := L) (coneWeight K) p.1).C_mul (z p)).pow (d p)
end GroundTheory.Heights₂.Heights.NumbersDVR.PointIdealMultiProj
