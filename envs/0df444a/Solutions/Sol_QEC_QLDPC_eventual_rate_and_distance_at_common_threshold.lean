-- Prove2me | solution 1 for QEC.QLDPC.eventual_rate_and_distance_at_common_threshold
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:28:57.276208+00:00
-- url     : https://prove2.me/submissions/b4a44f5e-4e6a-40f9-a5db-d06a20a11fb1

import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily

set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC
theorem _root_.solution
    (F : QuantumCodeFamily A ι κ) (rate relativeDistance : ℝ)
    (hRate : HasEventualRateAtLeast F rate)
    (hDistance : HasEventualRelativeDistanceAtLeast F relativeDistance) :
    ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
      rate * (F.blockLength a : ℝ) ≤ (F.encodedDimension a : ℝ) ∧
      relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ) := by
  obtain ⟨NRate, hRate⟩ := hRate
  obtain ⟨NDistance, hDistance⟩ := hDistance
  refine ⟨max NRate NDistance, ?_⟩
  intro a hLength
  exact ⟨hRate a (le_trans (le_max_left _ _) hLength),
    hDistance a (le_trans (le_max_right _ _) hLength)⟩
end QEC.QLDPC
