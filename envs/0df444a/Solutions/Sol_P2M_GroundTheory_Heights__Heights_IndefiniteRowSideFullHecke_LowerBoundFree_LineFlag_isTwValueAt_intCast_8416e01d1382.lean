-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_isTwValueAt_intCast_8416e01d1382
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:48:53.588575+00:00
-- url     : https://prove2.me/submissions/6590e2c5-158a-4176-84b0-050f42589156

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_IsPlueckerCoord
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HodgeLowerBound_PlueckerCoordinates_FlagLine
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_LowerBoundFree_LineFlag_isValueAt_intCast_d9a03a96e525

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
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
theorem _root_.solution (c : (k : Unit) → PBlk 2 k) (z : (Σ _ : Unit, Fin 2) → ℂ)
    (hz : ∀ k, z ⟨k, c k⟩ ≠ 0) (a : ℤ) : IsTwValueAt DL.y c 0 (a : Ω) z a :=
  ⟨hz, a, by rw [twistFactor_zero, mul_one]; exact isValueAt_intCast z a, by simp⟩
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree.LineFlag
