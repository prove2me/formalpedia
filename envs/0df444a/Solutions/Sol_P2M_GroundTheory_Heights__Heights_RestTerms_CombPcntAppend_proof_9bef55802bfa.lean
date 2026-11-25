-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombPcntAppend_proof_9bef55802bfa
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:32:36.92634+00:00
-- url     : https://prove2.me/submissions/6529e481-a559-4793-b576-87cac3bf60d2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombPcntAppend

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
open scoped Classical
open Comb
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombPcntAppend
theorem _root_.solution : CombPcntAppend.Statement := by
  intro m n q w s t i
  unfold pcnt
  rw [Finset.card_filter, Finset.card_filter, Finset.card_filter, Fin.sum_univ_add]
  congr 1
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_left, Fin.val_castAdd]
  · refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Fin.append_right, Fin.val_natAdd]
    have h : (n + (k : ℕ) < t) ↔ ((k : ℕ) < t - n) := by omega
    simp only [h]
end CombPcntAppend
end GroundTheory.Heights₂.Heights.RestTerms
