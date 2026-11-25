-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_WeierstrassPolynomialDivision_norm_pointWithLast_lt_b59f5ce14d21
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:31:26.803638+00:00
-- url     : https://prove2.me/submissions/85351308-7fa7-474d-8389-88a479af8800

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StWeierstrassPolynomialDivision
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_MonicDifferenceQuotient
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PWeierstrassPolynomialDivision

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open Topology Filter Metric Complex Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.WeierstrassPolynomialDivision
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.WeierstrassPolynomialDivision
theorem _root_.solution {σ : Type} [Fintype σ] {z : σ → ℂ} {s : ℂ} {ε : ℝ} (hε : 0 < ε) (hz : ‖z‖ < ε)
    (hs : ‖s‖ < ε) : ‖pointWithLast z s‖ < ε := by
  rw [pi_norm_lt_iff hε]
  intro o
  cases o with
  | none => exact hs
  | some i => exact (norm_le_pi_norm z i).trans_lt hz
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.WeierstrassPolynomialDivision
