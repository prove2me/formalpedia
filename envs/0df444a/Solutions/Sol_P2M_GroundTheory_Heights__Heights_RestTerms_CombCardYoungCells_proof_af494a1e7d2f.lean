-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCardYoungCells_proof_af494a1e7d2f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:32:10.44673+00:00
-- url     : https://prove2.me/submissions/bcb7ffee-7c2d-4177-802e-6b2fadb067e4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCardYoungCells

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.RestTerms
open Finset
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombCardYoungCells
theorem _root_.solution : CombCardYoungCells.Statement := by
  intro m lam
  classical
  unfold youngCells
  rw [Finset.card_filter, Finset.sum_product]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hle : lam i ≤ ∑ j, lam j :=
    Finset.single_le_sum (fun j _ => Nat.zero_le (lam j)) (Finset.mem_univ i)
  have hset : (Finset.range (∑ j, lam j)).filter (fun c => c < lam i) = Finset.range (lam i) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.card_range (lam i), ← hset, Finset.card_filter]
end CombCardYoungCells
end GroundTheory.Heights₂.Heights.RestTerms
