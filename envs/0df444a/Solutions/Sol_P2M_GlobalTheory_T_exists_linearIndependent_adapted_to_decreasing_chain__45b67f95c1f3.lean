-- Prove2me | solution 1 for P2M_GlobalTheory_T_exists_linearIndependent_adapted_to_decreasing_chain__45b67f95c1f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T04:54:09.093379+00:00
-- url     : https://prove2.me/submissions/439716e9-eb03-49b4-a1d2-806c700287d6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentAdaptedToDecreasingChainA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsLinearIndependentAdaptedToDecreasingChainAStatement
import Theorems.Thm_GlobalTheory_exists_linearIndependent_adapted_to_decreasing_chain


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (G : Type) [AddCommGroup G] [IsAddTorsionFree G] (S : ℕ → Set G), (∀ i, S (i + 1) ⊆ S i) → ∀ (N : ℕ) (r : ℕ → ℕ), (∀ i, ∃ e : Fin (r i) → G, LinearIndependent ℤ e ∧ ∀ j, e j ∈ S i) → (∀ i, r (i + 1) ≤ r i) → ∃ (e : Fin (r 0) → G) (n : Fin (r 0) → ℕ), LinearIndependent ℤ e ∧ (∀ j, e j ∈ S (n j)) ∧ ∑ i ∈ Finset.range (N + 1), r i ≤ ∑ j, (n j + 1) := by
  first | exact @GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | exact GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain | (intros; apply GlobalTheory.exists_linearIndependent_adapted_to_decreasing_chain <;> assumption)
end _root_.GlobalTheory.T
