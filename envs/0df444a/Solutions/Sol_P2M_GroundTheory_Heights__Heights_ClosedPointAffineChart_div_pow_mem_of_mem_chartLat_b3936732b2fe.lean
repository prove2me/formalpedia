-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ClosedPointAffineChart_div_pow_mem_of_mem_chartLat_b3936732b2fe
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:51:42.31883+00:00
-- url     : https://prove2.me/submissions/0a801c4f-9b7f-4ef0-a088-6ce799117961

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PCurveCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsClosedPointUnitSection
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PClosedPointChart

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
theorem _root_.solution {e : ℕ} {g : K'} (hg : g ∈ chartLat y 1 e) (t : T)
    (ht : y ⟨(), t⟩ ≠ 0) : g / y ⟨(), t⟩ ^ e ∈ chartRingZ y (fun _ => t) := by
  have h : g * ∏ k : Unit, y ⟨k, t⟩ ^ (-((e : ℤ) * (1 : Unit → ℤ) k)) ∈ chartRingZ y (fun _ => t) :=
    hg (fun _ => t) (fun _ => ht)
  simpa [zpow_neg, zpow_natCast, div_eq_mul_inv] using h
end GroundTheory.Heights₂.Heights.ClosedPointAffineChart
