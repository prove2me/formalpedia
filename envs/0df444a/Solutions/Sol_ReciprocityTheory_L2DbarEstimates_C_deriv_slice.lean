-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.C.deriv_slice
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:17:13.01022+00:00
-- url     : https://prove2.me/submissions/8f5dc6c8-badd-48ec-b24f-060c744d4e95

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_HoloWeakStatement
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_WeakHolomorphy_ExtCutA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.C
open MeasureTheory Metric Set Filter Topology Complex
open scoped ENNReal
noncomputable section
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates.C
theorem _root_.solution {Ω : Set (V n)} {F : V n → ℂ} (hΩ : IsOpen Ω) (hF : DifferentiableOn ℂ F Ω)
    {z e : V n} {l : ℂ} (hw : z + l • e ∈ Ω) :
    deriv (fun m : ℂ => F (z + m • e)) l = fderiv ℂ F (z + l • e) e := by
  have hd : DifferentiableAt ℂ F (z + l • e) := hF.differentiableAt (hΩ.mem_nhds hw)
  have hl : HasDerivAt (fun m : ℂ => z + m • e) e l := by
    simpa using ((hasDerivAt_id l).smul_const e).const_add z
  exact (hd.hasFDerivAt.comp_hasDerivAt l hl).deriv
end ReciprocityTheory.L2DbarEstimates.C
