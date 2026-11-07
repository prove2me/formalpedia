-- Prove2me | solution 1 for QEC.QLDPC.exists_large_good_member
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:43.41066+00:00
-- url     : https://prove2.me/submissions/ef70ce68-cd69-4ada-90fd-00ba9ee9703c

import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Theorems.Thm_QEC_QLDPC_eventual_rate_and_distance_at_common_threshold
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_exists_blockLength_ge


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC
theorem _root_.solution
    (F : QuantumCodeFamily A ι κ) (hGood : IsAsymptoticallyGoodQLDPCFamily F) :
    ∃ rate relativeDistance : ℝ, 0 < rate ∧ 0 < relativeDistance ∧
      ∀ M : Nat, ∃ a : A, M ≤ F.blockLength a ∧
        rate * (F.blockLength a : ℝ) ≤ (F.encodedDimension a : ℝ) ∧
        relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ) := by
  obtain ⟨_hLocality, ⟨rate, hRatePos, hRate⟩,
    ⟨relativeDistance, hDistancePos, hDistance⟩⟩ := hGood
  obtain ⟨N, hBoth⟩ :=
    eventual_rate_and_distance_at_common_threshold F rate relativeDistance hRate hDistance
  refine ⟨rate, relativeDistance, hRatePos, hDistancePos, ?_⟩
  intro M
  obtain ⟨a, ha⟩ := F.exists_blockLength_ge (max M N)
  exact ⟨a, le_trans (le_max_left _ _) ha,
    (hBoth a (le_trans (le_max_right _ _) ha)).1,
    (hBoth a (le_trans (le_max_right _ _) ha)).2⟩
end QEC.QLDPC
