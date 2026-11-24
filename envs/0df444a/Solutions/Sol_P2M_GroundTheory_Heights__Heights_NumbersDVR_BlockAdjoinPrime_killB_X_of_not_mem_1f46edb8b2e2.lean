-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_not_mem_1f46edb8b2e2
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:51.694985+00:00
-- url     : https://prove2.me/submissions/56e75f73-bb88-4d22-93c1-c2a0dcb497e9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PBlockAdjoinPrime

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
open GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
variable {R : Type*} [CommRing R] {K : Type*} {ι : K → Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
theorem _root_.solution (B : Set K) {v : Σ k, ι k} (hv : v.1 ∉ B) :
    killB (R := R) B (X v) = X v := by
  classical
  simp [killB, hv]
end GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
