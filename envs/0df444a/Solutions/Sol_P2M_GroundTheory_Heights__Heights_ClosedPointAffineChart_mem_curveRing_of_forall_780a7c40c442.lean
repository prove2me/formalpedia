-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_mem_curveRing_of_forall_780a7c40c442
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:29:46.348513+00:00
-- url     : https://prove2.me/submissions/ee603f3a-6e14-4974-9d3d-5cc0e6ac7311

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
theorem _root_.solution {b : K'}
    (h : ∀ t : T, y ⟨(), t⟩ ≠ 0 → b ∈ chartRingZ y (fun _ => t)) : b ∈ curveRing y := by
  rw [mem_curveRing]
  intro c hc
  have hc' : c = fun _ => c () := funext fun u => by cases u; rfl
  have h1 := h (c ()) (hc ())
  rwa [← hc'] at h1
end GroundTheory.Heights₂.Heights.ClosedPointAffineChart
