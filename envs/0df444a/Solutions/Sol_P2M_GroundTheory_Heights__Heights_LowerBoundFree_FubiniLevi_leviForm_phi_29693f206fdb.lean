-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_leviForm_phi_29693f206fdb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T05:24:57.104288+00:00
-- url     : https://prove2.me/submissions/2d8f5cee-a24d-405b-bc42-52f6701b1cfc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_FubiniLevi
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_FubiniLevi_fderiv_fderiv_phi_0e0a76ba56ea

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
theorem _root_.solution {z : J → ℂ} (hz : sqSum z ≠ 0) (w : J → ℂ) :
    leviForm phi z w = (sqSum z * sqSum w - (reInner z w ^ 2 + reInner z (Complex.I • w) ^ 2)) /
      (2 * sqSum z ^ 2) := by
  have hw : sqSum (Complex.I • w) = sqSum w := by
    simp [sqSum]
  unfold leviForm
  rw [fderiv_fderiv_phi hz, fderiv_fderiv_phi hz, hw]
  field_simp
  ring
end GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi
