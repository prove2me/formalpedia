-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_gramVol_const_zero_81197df01573
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:56:39.759953+00:00
-- url     : https://prove2.me/submissions/2d6e75ac-6d94-4cb5-8815-78d6bdbcab8e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StConeSheetGramLintegral
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_LogIntegrableOnOfLogIntegrable
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeSheetArea
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PConeSheetGram

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory Matrix ComplexSets
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {e n : ℕ} (y : Fin e → ℂ) :
    gramVol (fun _ : Fin e → ℂ => (0 : Fin n → ℂ)) y = 0 := by
  unfold gramVol
  have hw : (Fin.cons 0 (fun _ => 0) : Fin (e + 1) → Fin n → ℂ) = 0 := by
    funext a
    refine Fin.cases ?_ (fun j => ?_) a <;> simp
  have h0 : (Matrix.of fun (_ _ : Fin (e + 1)) => (0 : ℂ)).det = 0 := Matrix.det_zero
  simp [hw, h0]
end GroundTheory.Heights₂.Heights
