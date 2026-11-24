-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_isDegZeroSmooth_log_6908ea6c59be
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:50.231158+00:00
-- url     : https://prove2.me/submissions/e73368f5-595d-4e57-b204-e63a2c31d157

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterRedF
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_OrbitLimits_StokesObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {B : HermLine ι} (hB : IsSmoothHerm B) (h0 : B.a = 0) :
    IsDegZeroSmooth (fun z => Real.log (B.h z)) := by
  refine ⟨ContDiffOn.log hB fun z hz => (B.pos z hz).ne', fun c z hc => ?_⟩
  simp only [B.smul c z hc, h0, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
end GroundTheory.Heights₂.Heights
