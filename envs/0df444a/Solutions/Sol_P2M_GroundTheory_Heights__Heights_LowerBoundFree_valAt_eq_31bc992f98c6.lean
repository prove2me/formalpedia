-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_valAt_eq_31bc992f98c6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T05:25:00.674405+00:00
-- url     : https://prove2.me/submissions/84fc7e74-e5e7-4f5a-a0db-bf9c28fff5e1

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LowerBoundFree_isValueAt_unique_d279c6dbe068

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
variable {Ω : Type} [Field Ω]
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {y : (Σ k, ι k) → Ω} {s : Ω} {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ mcPts (mCoordIdeal y)) {v : ℂ} (hv : IsValueAt y s z v) : valAt y s z = v := by
  classical
  have h : ∃ v, IsValueAt y s z v := ⟨v, hv⟩
  rw [valAt, dif_pos h]
  exact isValueAt_unique hz h.choose_spec hv
end GroundTheory.Heights₂.Heights.LowerBoundFree
