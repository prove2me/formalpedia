-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LowerBoundFree_prod_norm_zpow_pos_0010832a9c82
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:04:28.829716+00:00
-- url     : https://prove2.me/submissions/afc6aa4a-3bd4-4bd0-a409-a5c090a4296a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_CoordinateIdeals_MemMCoordIdealOfAevalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_FrameDefinitions_Metric

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
namespace GroundTheory.Heights₂.Heights.LowerBoundFree
theorem _root_.solution {c : K → ℂ} (hc : ∀ k, c k ≠ 0) (a : K → ℤ) : 0 < ∏ k, ‖c k‖ ^ a k :=
  Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hc k)) _
end GroundTheory.Heights₂.Heights.LowerBoundFree
