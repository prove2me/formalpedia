-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mat_mulVec_b5e90605ff3e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:12:42.997448+00:00
-- url     : https://prove2.me/submissions/1cedfdc3-c11a-4f90-9ddd-beba8c4f633c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_segre_lift_bc08ad365c4d

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
open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar IsGoodProj mcPts fibre segre)
open Matrix
open GroundTheory.Heights₂.Heights.ConeLocalSheets
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ConeLocalSheets
theorem _root_.solution (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (z : Fin n → ℂ) :
    LinearMap.toMatrix' (lin Ψ) *ᵥ z = Ψ (segre (lift z)) := by
  rw [LinearMap.toMatrix'_mulVec, segre_lift]
  rfl
end GroundTheory.Heights₂.Heights.ConeLocalSheets
