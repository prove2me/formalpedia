-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.intOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:15:05.944043+00:00
-- url     : https://prove2.me/submissions/2f102988-b804-444d-9c67-bc33ff7dcdd9

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_FrameEstimates_CoefSumA
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_bdd
import Theorems.Thm_PositivityTheory_ThKEst_CS_Dual_fin

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
theorem _root_.solution (h : Dual r e) (hD : IsAddFundamentalDomain r.range D μ) {g : G → ℂ} (hg : Continuous g)
    (hp : ∀ ξ u, g (r ξ + u) = g u) : IntegrableOn g D μ := by
  obtain ⟨C, hC⟩ := h.bdd hg hp
  exact Measure.integrableOn_of_bounded (h.fin hD) hg.aestronglyMeasurable (M := C) (Eventually.of_forall hC)
end Dual
end PositivityTheory.ThKEst.CS
