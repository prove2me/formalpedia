-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveCharts_proof_f79ca0f4cf98
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T06:10:06.11522+00:00
-- url     : https://prove2.me/submissions/def14b33-5549-4866-8999-5f70f8551a9b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finite_1e9464aa5696
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_CurveAffineCharts_finrank_eq_e3e2ee841f1e

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
open ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I4 NumberField IsDedekindDomain
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace CurveCharts
theorem _root_.solution (hc : ClosedPointChart.Statement) : CurveCharts.Statement :=
  fun T _ K' _ _ y hy =>
    ⟨CurveAffineCharts.finite y hy, CurveAffineCharts.finrank_eq y hy, hc T K' y hy⟩
end CurveCharts
end GroundTheory.Heights₂.Heights
