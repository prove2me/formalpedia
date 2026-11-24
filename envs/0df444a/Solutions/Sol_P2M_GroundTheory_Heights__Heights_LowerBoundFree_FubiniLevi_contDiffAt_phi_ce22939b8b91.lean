-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_contDiffAt_phi_ce22939b8b91
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:03:00.567011+00:00
-- url     : https://prove2.me/submissions/67b36882-30dd-439b-b251-f23703c4abff

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
open ReciprocityTheory.ChartRestriction.G.Geo Filter Topology
variable {J : Type} [Fintype J]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
theorem _root_.solution {z : J → ℂ} (hz : sqSum z ≠ 0) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n phi z := by
  have hs : ContDiff ℝ n (sqSum : (J → ℂ) → ℝ) :=
    ContDiff.sum fun p _ => (contDiff_norm_sq ℝ).comp (contDiff_apply ℝ ℂ p)
  exact (hs.contDiffAt.log hz).mul contDiffAt_const
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
