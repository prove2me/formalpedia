-- Prove2me | solution 1 for TranslationOuter.simpleProbability_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T23:12:52.903098+00:00
-- url     : https://prove2.me/submissions/2eafeaaa-e977-4397-9132-ad984c50e7ef

module
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Algebra.Order.Star.Real
public import Mathlib.Data.Int.Star
public import Mathlib.Combinatorics.Graph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.GroupTheory.OrderOfElement
public import Mathlib.Tactic.FinCases
public import Definitions.Def_BirthdayNonbacktracking_Solution
public import Theorems.Thm_card_walkCount
public import Theorems.Thm_TranslationOuter_simpleWalkCount_le_walkCount

set_option autoImplicit true
@[expose] public section
public section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
set_option linter.unusedSectionVars false
open TranslationOuter
open GeneralFinalRatio
noncomputable section
universe u
namespace TranslationOuter
theorem _root_.solution
    {V : Type u} [Fintype V]
    (d : ℕ) [NeZero d] (hd : 3 ≤ d)
    (G : SimpleGraph V) (hG : IsRegularOfDegree G d)
    (start : OrientedEdge G) (k : ℕ) (hk : 0 < k) :
    simpleProbability G start k ≤ 1 := by
  have hk1 : 1 ≤ k := hk
  have hwalkNat : 0 < walkCount G start k := by
    rw [card_walkCount d G hG start k hk1]
    exact pow_pos (by omega) _
  have hwalkReal : (0 : ℝ) < walkCount G start k := by
    exact_mod_cast hwalkNat
  rw [simpleProbability]
  apply (div_le_iff₀ hwalkReal).2
  norm_num
  exact_mod_cast simpleWalkCount_le_walkCount G start k
end TranslationOuter
