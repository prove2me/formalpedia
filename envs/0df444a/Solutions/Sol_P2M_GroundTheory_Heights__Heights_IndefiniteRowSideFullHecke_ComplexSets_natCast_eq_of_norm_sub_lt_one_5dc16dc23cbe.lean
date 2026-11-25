-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_natCast_eq_of_norm_sub_lt_one_5dc16dc23cbe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:09:20.814327+00:00
-- url     : https://prove2.me/submissions/1464c99a-34e0-44a5-b85e-c4ca900c8f38

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StGermWeierstrassPreparation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParametricCircleIntegralAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StCircleArgumentPrinciple
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StPowerSumsEsymmAnalytic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGermWeierstrassPreparation

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
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
theorem _root_.solution {m n : ℕ} (h : ‖(m : ℂ) - n‖ < 1) : m = n := by
  have h' : |(m : ℝ) - n| < 1 := by
    have e : ((m : ℂ) - n) = (((m : ℝ) - n : ℝ) : ℂ) := by push_cast; ring
    rwa [e, Complex.norm_real, Real.norm_eq_abs] at h
  rw [abs_lt] at h'
  have h1 : m < n + 1 := by exact_mod_cast (show (m : ℝ) < n + 1 by linarith)
  have h2 : n < m + 1 := by exact_mod_cast (show (n : ℝ) < m + 1 by linarith)
  omega
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
