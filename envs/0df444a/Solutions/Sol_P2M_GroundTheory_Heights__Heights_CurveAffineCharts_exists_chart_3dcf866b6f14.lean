-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_CurveAffineCharts_exists_chart_3dcf866b6f14
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:27:35.868105+00:00
-- url     : https://prove2.me/submissions/303a3caa-2ec8-4030-95eb-b84b5ef0acbc

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsPointVertRSteps
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts

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
open GroundTheory.Heights₂.Heights.CurveAffineCharts
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
namespace GroundTheory.Heights₂.Heights.CurveAffineCharts
theorem _root_.solution (hy : IsArithVar (mCoordIdeal y) 1) : ∃ t : T, y ⟨(), t⟩ ≠ 0 := by
  obtain ⟨t, ht⟩ := hy.2.1.2.2 ()
  refine ⟨t, fun h0 => ht ?_⟩
  simp [mCoordIdeal, RingHom.mem_ker, mConeMap, h0]
end GroundTheory.Heights₂.Heights.CurveAffineCharts
