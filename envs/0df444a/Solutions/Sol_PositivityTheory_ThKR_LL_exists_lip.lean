-- Prove2me | solution 1 for PositivityTheory.ThKR.LL.exists_lip
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:13:00.947865+00:00
-- url     : https://prove2.me/submissions/468835ab-3d34-4dbc-b362-568c056d1871

import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_IsoOfIntegral
import Definitions.Def_Development_WeilBound_ThetaLifts_Reductions_NormExpSubLe

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Complex SchwartzMap Matrix GlobalTheory.RealWeil PositivityTheory.ThKF.E Filter Topology
open scoped Real RealInnerProductSpace FourierTransform
open PositivityTheory PositivityTheory.ThKR PositivityTheory.ThKR.LL
variable {l : Type} [Fintype l]
namespace PositivityTheory.ThKR.LL
theorem _root_.solution {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] {S : ℝ → F} {S' : F} {t₀ : ℝ}
    (h : HasDerivAt S S' t₀) : ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ t in 𝓝 t₀, ‖S t - S t₀‖ ≤ K * |t - t₀| := by
  obtain ⟨K, hK, h⟩ := h.isBigO_sub.exists_nonneg
  exact ⟨K, hK, h.bound⟩
end PositivityTheory.ThKR.LL
