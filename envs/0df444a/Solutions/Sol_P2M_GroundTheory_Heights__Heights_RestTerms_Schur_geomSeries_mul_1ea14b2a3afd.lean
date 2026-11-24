-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_Schur_geomSeries_mul_1ea14b2a3afd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T18:35:15.543855+00:00
-- url     : https://prove2.me/submissions/fc272425-a2f2-4874-a032-5a86f3bbd13f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_JacobiTrudi

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms GroundTheory.Heights₂.Heights.RestTerms.Schur
open MvPolynomial Finset
noncomputable section
variable {R : Type*} [CommRing R]
namespace GroundTheory.Heights₂.Heights.RestTerms.Schur
theorem _root_.solution (a : R) :
    geomSeries a * (1 - PowerSeries.C a * PowerSeries.X) = 1 := by
  ext n
  rw [mul_sub, mul_one, map_sub, ← mul_assoc, mul_comm (geomSeries a) (PowerSeries.C a)]
  rcases n with _ | n
  · simp [geomSeries]
  · rw [PowerSeries.coeff_succ_mul_X, PowerSeries.coeff_C_mul]
    simp [geomSeries, pow_succ, mul_comm]
end GroundTheory.Heights₂.Heights.RestTerms.Schur
