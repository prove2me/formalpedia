-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_fromPoly_cx_85517b06cadd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:56:47.299443+00:00
-- url     : https://prove2.me/submissions/ea835f1e-d974-4e1c-a260-93bdaeca5240

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_ComapMaximalIdealParDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_VerticalDivisors_PChartDomain
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Vertical_ChartDomain_baseToChart_mk_793326c29cbf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Vertical
open MvPolynomial
noncomputable section
open GroundTheory.Heights₂.Heights.Vertical.ChartDomain
variable {D : Type} [CommRing D] {n e : ℕ} (Q : Ideal (MvPolynomial (Fin n) D)) (j : Fin n)
namespace GroundTheory.Heights₂.Heights.Vertical.ChartDomain
theorem _root_.solution (l : Fin n) : fromPoly Q j e (cx Q j e l) = toChart Q j e (X l) := by
  rw [cx, fromPoly, coe_eval₂Hom, eval₂_C, baseToChart_mk, map_X]
end GroundTheory.Heights₂.Heights.Vertical.ChartDomain
