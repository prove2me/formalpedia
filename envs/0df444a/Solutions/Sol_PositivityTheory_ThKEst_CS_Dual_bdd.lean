-- Prove2me | solution 1 for PositivityTheory.ThKEst.CS.Dual.bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:51.92891+00:00
-- url     : https://prove2.me/submissions/f5eefac0-d88a-4285-9f47-017d53623a4c

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
omit [IsTopologicalAddGroup G]
namespace PositivityTheory.ThKEst.CS
namespace Dual
theorem _root_.solution (h : Dual r e) {g : G → ℂ} (hg : Continuous g) (hp : ∀ ξ u, g (r ξ + u) = g u) :
    ∃ C, ∀ u, ‖g u‖ ≤ C := by
  obtain ⟨K, hK, hKc⟩ := h.cpt
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun u => ?_⟩
  obtain ⟨ξ, hξ⟩ := hKc u
  have e : g u = g (u - r ξ) := by rw [← hp ξ (u - r ξ), add_sub_cancel]
  rw [e]
  exact hC _ hξ
end Dual
end PositivityTheory.ThKEst.CS
