-- Prove2me | solution 1 for QEC.QLDPC.eventual_two_sided_distance_bounds
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:47:24.394719+00:00
-- url     : https://prove2.me/submissions/3480b428-e334-46ba-8454-5d361b1cb237

import Definitions.Def_QEC_Coding_QLDPC_QuantumCodeFamily
import Definitions.Def_QEC_Coding_QLDPC_AsymptoticallyGoodFamily
import Theorems.Thm_QEC_QLDPC_FiniteQuditCheckPresentation_distance_le_blockLength
import Theorems.Thm_QEC_QLDPC_QuantumCodeFamily_distance_le_blockLength


set_option autoImplicit false
noncomputable section
open QEC QEC.QLDPC
universe u v w
variable {A : Type u} {ι : A → Type v} {κ : A → Type w}
variable [∀ a, Fintype (ι a)] [∀ a, DecidableEq (ι a)] [∀ a, Fintype (κ a)]
namespace QEC.QLDPC
theorem _root_.solution
    (F : QuantumCodeFamily A ι κ) (relativeDistance : ℝ)
    (hDistance : HasEventualRelativeDistanceAtLeast F relativeDistance) :
    ∃ N : Nat, ∀ a, N ≤ F.blockLength a →
      relativeDistance * (F.blockLength a : ℝ) ≤ (F.distance a : ℝ) ∧
        (F.distance a : ℝ) ≤ (F.blockLength a : ℝ) := by
  obtain ⟨N, hN⟩ := hDistance
  refine ⟨N, fun a ha => ⟨hN a ha, ?_⟩⟩
  exact_mod_cast F.distance_le_blockLength a
end QEC.QLDPC
