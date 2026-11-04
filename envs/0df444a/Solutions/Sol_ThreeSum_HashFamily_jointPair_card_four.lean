-- Prove2me | solution 1 for ThreeSum.HashFamily.jointPair_card_four
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T11:19:52.789705+00:00
-- url     : https://prove2.me/submissions/5b5cc52d-0982-4725-b0f5-7bc74eb759d9

import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Definitions.Def_Submission_ThreeSum_HashFamily
import Theorems.Thm_ThreeSum_HashFamily_oneHot_four_independent
import Theorems.Thm_ThreeSum_HashFamily_hashMap_apply
import Theorems.Thm_ThreeSum_HashFamily_wordEvent_card
attribute [local simp] ThreeSum.HashFamily.hashMap_apply

set_option autoImplicit false
open ThreeSum ThreeSum.HashFamily
open scoped BigOperators
variable {α K : Type*}
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]
namespace ThreeSum.HashFamily
theorem _root_.solution {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) (a b : K) :
    Fintype.card K ^ 4 * (pairEvent s t a b ∩ pairEvent u v a b).card =
      Fintype.card (α × Bool → K) := by
  have he : pairEvent s t a b ∩ pairEvent u v a b =
      wordEvent ![s, t, u, v] ![a, b, a, b] := by
    ext w
    simp [pairEvent, wordEvent, Fin.forall_fin_succ, and_assoc]
  rw [he]
  apply wordEvent_card
  convert oneHot_four_independent (K := K) hst hsu hsv htu htv huv hm using 1
  funext i
  fin_cases i <;> rfl
end ThreeSum.HashFamily
