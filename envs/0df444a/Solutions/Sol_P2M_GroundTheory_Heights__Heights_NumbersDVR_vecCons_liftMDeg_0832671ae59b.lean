-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_vecCons_liftMDeg_0832671ae59b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:44:49.296982+00:00
-- url     : https://prove2.me/submissions/b14d7025-ceb6-446e-a6db-7ace28870a24

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_BlowUpPushHypothesesExample
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_CycEvalCongrOnSupport

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
universe u
variable {K : Type*} [Fintype K] [DecidableEq K] {ι : K → Type} {R : Type*} [CommRing R]
omit [Fintype K] [DecidableEq K]
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution {d : ℕ} (c : K → ℕ) (L : Fin d → K → ℤ) :
    Matrix.vecCons (fun k => ((liftMDeg c k : ℕ) : ℤ)) (liftDegs L) =
      liftDegs (Matrix.vecCons (fun k => (c k : ℤ)) L) := by
  funext i o
  refine Fin.cases ?_ (fun i => ?_) i <;> cases o <;> simp [liftDegs, liftDeg, liftMDeg]
end GroundTheory.Heights₂.Heights.NumbersDVR
