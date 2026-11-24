-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_chart_of_mem_curveRing_93a3946b1876
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:42.201026+00:00
-- url     : https://prove2.me/submissions/366c618b-87ae-4fa1-ab13-9729971744a8

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointChart
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_mem_curveRing_46da28e9018f


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
open ReciprocityTheory.ChartRestriction.G.Geo
noncomputable section
open GroundTheory.Heights₂.Heights.ClosedPointAffineChart
variable {T : Type} [Fintype T] {K' : Type} [Field K'] (y : (Σ _ : Unit, T) → K')
omit [Fintype T]
namespace GroundTheory.Heights₂.Heights.ClosedPointAffineChart
theorem _root_.solution {b : K'} (hb : b ∈ curveRing y) (t : T) (ht : y ⟨(), t⟩ ≠ 0) :
    b ∈ chartRingZ y (fun _ => t) :=
  mem_curveRing.mp hb (fun _ => t) (fun _ => ht)
end GroundTheory.Heights₂.Heights.ClosedPointAffineChart
