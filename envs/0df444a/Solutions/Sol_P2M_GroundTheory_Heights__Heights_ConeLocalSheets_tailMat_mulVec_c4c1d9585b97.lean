-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ConeLocalSheets_tailMat_mulVec_c4c1d9585b97
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:20:39.248092+00:00
-- url     : https://prove2.me/submissions/11837454-5920-498f-a6f3-a1dcee830647

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsConeLocalSheets
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsQuasiFiniteSheets
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterFib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_PConeLocalSheets
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ConeLocalSheets_mat_mulVec_b5e90605ff3e

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
theorem _root_.solution (Ψ : (((k : Unit) → PBlk n k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (z : Fin n → ℂ)
    (i : Fin e) : (tailMat Ψ *ᵥ z) i = Ψ (segre (lift z)) i.succ := by
  rw [← mat_mulVec]
  simp [tailMat, Matrix.mulVec, dotProduct]
end GroundTheory.Heights₂.Heights.ConeLocalSheets
