-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.orderedInsertQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:38:11.833598+00:00
-- url     : https://prove2.me/submissions/e46f9e95-c2c1-48ec-828d-35e8a43fd5b5

import Mathlib.Data.List.Sort
import Mathlib.Data.List.Basic
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedLists

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {A : Type*} (cmp : A → A → Bool × ℕ) (C : ℕ)
    (hc : ∀ a b, (cmp a b).2 ≤ C) (a : A) (L : List A) :
    (orderedInsertQuery cmp a L).2 ≤ (L.length+1)*(C+1) := by
  induction L with
  | nil => simp [orderedInsertQuery]
  | cons b L ih =>
    have hb := hc a b
    simp only [orderedInsertQuery,List.length_cons]
    split_ifs <;> simp only [Prod.snd]
    all_goals nlinarith
end QEC.Coding.BDL26RandomPerturbation
