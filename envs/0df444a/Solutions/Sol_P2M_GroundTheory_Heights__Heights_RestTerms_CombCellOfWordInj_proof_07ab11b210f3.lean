-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_RestTerms_CombCellOfWordInj_proof_07ab11b210f3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:34:21.930184+00:00
-- url     : https://prove2.me/submissions/e7ccce46-7031-45e4-a50c-b9e9459350b2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_StatementsComb
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_RemainderTerms_PCombCellOfWordInj
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_RestTerms_Comb_pcnt_lt_of_lt_of_eq_cf8434a17462

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
open Finset Comb
namespace GroundTheory.Heights₂.Heights.RestTerms
namespace CombCellOfWordInj
theorem _root_.solution : CombCellOfWordInj.Statement := by
  intro m n w s t h
  simp only [cellOfWord, Prod.mk.injEq] at h
  obtain ⟨hw, hc⟩ := h
  by_contra hne
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have := Comb.pcnt_lt_of_lt_of_eq w hlt (w s) rfl
    rw [hc, hw] at this
    exact lt_irrefl _ (hw ▸ this)
  · have := Comb.pcnt_lt_of_lt_of_eq w hlt (w t) rfl
    rw [← hc, ← hw] at this
    exact lt_irrefl _ (hw ▸ this)
end CombCellOfWordInj
end GroundTheory.Heights₂.Heights.RestTerms
