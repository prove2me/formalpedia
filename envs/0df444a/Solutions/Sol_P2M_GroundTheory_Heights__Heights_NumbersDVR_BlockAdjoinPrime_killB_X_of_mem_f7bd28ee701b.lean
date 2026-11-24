-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_BlockAdjoinPrime_killB_X_of_mem_f7bd28ee701b
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:41:51.774083+00:00
-- url     : https://prove2.me/submissions/f24185e3-c66e-4c04-8318-d25f5696b6e7

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
theorem _root_.solution (B : Set K) {v : Σ k, ι k} (hv : v.1 ∈ B) :
    killB (R := R) B (X v) = 0 := by
  classical
  simp [killB, hv]
end GroundTheory.Heights₂.Heights.NumbersDVR.BlockAdjoinPrime
