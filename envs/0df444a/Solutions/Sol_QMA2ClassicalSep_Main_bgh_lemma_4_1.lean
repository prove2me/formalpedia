-- Prove2me | solution 1 for QMA2ClassicalSep.Main.bgh_lemma_4_1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T03:39:14.433388+00:00
-- url     : https://prove2.me/submissions/3e6aab1a-61ee-48b9-954b-931598b657bb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_QMA2ClassicalSep_Main_HardDist
import Theorems.Thm_QMA2ClassicalSep_Main_bgh_product_overlap

open scoped BigOperators ComplexConjugate
open Matrix
open QMA2ClassicalSep.Main

theorem solution (N : ℕ) : hSep (projAlt N) ≤ 1 / 3 := by
  classical
  unfold hSep
  by_cases hne : {e : ℝ | ∃ α β : Fin N × Fin N → ℂ,
      IsUnit' α ∧ IsUnit' β ∧ e = expect (projAlt N) (fun i => α i.1 * β i.2)}.Nonempty
  · apply csSup_le hne
    intro e he
    rcases he with ⟨α, β, hα, hβ, rfl⟩
    exact bgh_product_overlap N α β hα hβ
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    norm_num
