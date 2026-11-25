-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsGandhiFirst.eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:04:50.687412+00:00
-- url     : https://prove2.me/submissions/2dd98a1a-06ae-460f-82fc-048755d16c68

module
public import Definitions.Def_PretorsionImageClosed_Statement
public import Mathlib.Tactic.LinearCombination
public import Definitions.Def_PretorsionImageClosed_Gandhi_Delta
public import Theorems.Thm_PretorsionImageClosed_Statement_IsDelta_unique

set_option autoImplicit true
@[expose] public section
public section
set_option autoImplicit false
noncomputable section
open PretorsionImageClosed PretorsionImageClosed.Statement
open Polynomial
namespace PretorsionImageClosed.Statement
namespace IsGandhiFirst
theorem _root_.solution {B B' : ℕ → Rq[X]} (hB : IsGandhiFirst B) (hB' : IsGandhiFirst B') :
    ∀ m, 1 ≤ m → B m = B' m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    cases m with
    | zero => rw [hB.1, hB'.1]
    | succ m =>
      have h1 := hB.2 (m + 2) (by omega)
      have h2 := hB'.2 (m + 2) (by omega)
      have hm : m + 2 - 1 = m + 1 := rfl
      rw [hm] at h1 h2
      rw [ih (by omega)] at h1
      exact h1.unique h2
end IsGandhiFirst
end PretorsionImageClosed.Statement
