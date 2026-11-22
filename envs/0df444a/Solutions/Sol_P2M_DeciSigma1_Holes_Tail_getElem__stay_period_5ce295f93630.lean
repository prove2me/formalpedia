-- Prove2me | solution 1 for P2M_DeciSigma1_Holes_Tail_getElem__stay_period_5ce295f93630
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:53:00.114815+00:00
-- url     : https://prove2.me/submissions/bbaa0803-f947-45b2-8a98-fe604780ae11

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Arithmetic_DifferenceConstraints
public import Definitions.Def_LeanPool_DeciSigma1_Words_Basic
public import Definitions.Def_LeanPool_DeciSigma1_Words_SuffixChains
public import Mathlib.Order.Nat
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Theorems.Thm_P2M_DeciSigma1_Holes_Tail_getElem__pumpFactor_ge_c1284156d4c1

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Readers
open DeciSigma1.Words (pow)
open DeciSigma1.Readers.Table
variable {α S : Type} {k : ℕ}
variable {x : List α} {c c' L : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (hcc : c < c') (hc' : c' ≤ x.length) {p : ℕ} (hc : c ≤ p)
    (hp : p + (c' - c) < c + L) :
    (pumpFactor x c c' L)[p + (c' - c)]? = (pumpFactor x c c' L)[p]? := by
  rw [getElem?_pumpFactor_ge hcc hc' (by omega) hp, getElem?_pumpFactor_ge hcc hc' hc (by omega)]
  congr 2
  rw [show p + (c' - c) - c = p - c + (c' - c) by omega, Nat.add_mod_right]
end DeciSigma1.Holes.Tail
