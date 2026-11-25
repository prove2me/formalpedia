-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombVandermondeSucc_proof_86b0dd0a45b1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:58:19.782999+00:00
-- url     : https://prove2.me/submissions/25dfa764-5428-40a4-a56f-a6824b3ca6b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombVandermondeSucc

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
namespace CombVandermondeSucc
theorem _root_.solution : CombVandermondeSucc.Statement := by
  intro n v
  unfold vandermondeOf
  have hI : ∀ {k : ℕ} (i : Fin k), Ioi i = univ.filter (fun j => i < j) := by
    intro k i; ext j; simp
  simp only [hI, Finset.prod_filter]
  rw [Fin.prod_univ_succ]
  congr 1
  · rw [Fin.prod_univ_succ]
    simp [Fin.succ_pos]
  · refine Finset.prod_congr rfl (fun i _ => ?_)
    rw [Fin.prod_univ_succ]
    simp [Fin.succ_lt_succ_iff]
end CombVandermondeSucc
end GroundTheory.Heights₂.Heights.RestTerms
