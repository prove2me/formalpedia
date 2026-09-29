-- Prove2me | solution 1 for TarchaBraids.standardPureBraidWord_list_transport_v1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-22T21:51:58.359301+00:00
-- url     : https://prove2.me/submissions/926ce258-cec3-4b11-b7cd-7a30245203a4

import Mathlib
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
import Theorems.Thm_TarchaBraids_standardPureBraidWord_higher_filter_succ_v1

open TarchaBraids

/-- The classical pure-braid signed list obeys far-right strand transport:
    the new final half-twist, the lifted old word, then its inverse. -/
theorem solution (n : ℕ) (j : Fin n) :
    standardPureBraidWord (n + 1) j.castSucc =
      [{ index := (Fin.last n : Fin (n + 2 - 1)),
         sign := BraidLetterSign.positive }] ++
      (standardPureBraidWord n j).map
        (fun a : BraidLetter (n + 1) =>
          ({ index := Fin.castLE (by omega) a.index, sign := a.sign } :
             BraidLetter (n + 2))) ++
      [{ index := (Fin.last n : Fin (n + 2 - 1)),
         sign := BraidLetterSign.negative }] := by
  have hfilter := TarchaBraids.standardPureBraidWord_higher_filter_succ_v1 n j
  simp only [standardPureBraidWord]
  rw [hfilter]
  simp [List.reverse_append, List.map_append, List.map_map,
    List.append_assoc, Function.comp_def, Fin.castLE, Fin.castSucc, Fin.castAdd, Fin.cast]
