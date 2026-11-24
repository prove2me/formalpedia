-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.lint
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:21:35.878017+00:00
-- url     : https://prove2.me/submissions/618fcba6-b898-4b3e-91ed-405660f32ca9

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Topology Filter
open scoped ENNReal ComplexConjugate Pointwise
open PositivityTheory PositivityTheory.ThKEst PositivityTheory.ThKEst.CS
variable {G Γ : Type} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G] [AddCommGroup Γ]
variable {r : Γ →+ G} {e : Γ → G → ℂ}
variable [MeasurableSpace G] [BorelSpace G] [Countable Γ] {μ : Measure G} [μ.IsAddHaarMeasure] {D : Set G}
namespace PositivityTheory.ThKEst.CS
namespace Dual
theorem _root_.solution (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) (f : G → ℝ≥0∞) :
    ∫⁻ u, f u ∂μ = ∑' ξ, ∫⁻ u in D, f (r ξ + u) ∂μ := by
  rw [hD.lintegral_eq_tsum'' f, ← (AddMonoidHom.ofInjective h.inj).toEquiv.tsum_eq]
  rfl
end Dual
end PositivityTheory.ThKEst.CS
