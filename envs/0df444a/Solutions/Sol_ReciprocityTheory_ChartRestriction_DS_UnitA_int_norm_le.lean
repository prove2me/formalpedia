-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.UnitA.int_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:15:19.022384+00:00
-- url     : https://prove2.me/submissions/f3e084b8-4a45-4c1f-8acb-532e94fa50b1

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_UnitarizeA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped ENNReal ComplexConjugate
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.UnitA
variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
  [BorelSpace G] [SecondCountableTopology G] (μ : Measure G)
variable {μ}
namespace ReciprocityTheory.ChartRestriction.DS.UnitA
theorem _root_.solution {a b : G → ℂ} (ha : MemLp a 2 μ) (hb : MemLp b 2 μ) :
    ∫ x, ‖star (a x) * b x‖ ∂μ ≤ nrm μ a * nrm μ b := by
  have hA : MemLp (fun x => ‖a x‖) 2 μ := ha.norm
  have hB : MemLp (fun x => ‖b x‖) 2 μ := hb.norm
  have h1 : ∫ x, ‖star (a x) * b x‖ ∂μ = inner ℝ (hA.toLp _) (hB.toLp _) := by
    rw [MeasureTheory.L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hA.coeFn_toLp, hB.coeFn_toLp] with x hx1 hx2
    rw [hx1, hx2, RCLike.inner_apply, norm_mul, norm_star]
    simp only [starRingEnd_apply, star_trivial]
    ring
  rw [h1]
  calc inner ℝ (hA.toLp _) (hB.toLp _) ≤ ‖hA.toLp _‖ * ‖hB.toLp _‖ := real_inner_le_norm _ _
    _ = nrm μ a * nrm μ b := by
      simp only [nrm, Lp.norm_toLp, eLpNorm_norm]
end ReciprocityTheory.ChartRestriction.DS.UnitA
