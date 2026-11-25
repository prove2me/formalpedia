-- Prove2me | solution 1 for PretorsionImageClosed.Statement.IsGandhiSecond.eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:05:30.23494+00:00
-- url     : https://prove2.me/submissions/98f22797-b2a5-46df-9206-39c672eee49b

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
namespace IsGandhiSecond
theorem _root_.solution {Cs Cs' : ℕ → Rq[X]} (hC : IsGandhiSecond Cs) (hC' : IsGandhiSecond Cs') :
    ∀ m, 1 ≤ m → Cs m = Cs' m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ m ih =>
    intro _
    cases m with
    | zero => rw [hC.1, hC'.1]
    | succ m =>
      obtain ⟨g, hg, hCg⟩ := hC.2 (m + 2) (by omega)
      obtain ⟨g', hg', hCg'⟩ := hC'.2 (m + 2) (by omega)
      have hm : m + 2 - 1 = m + 1 := rfl
      rw [hm] at hg hg'
      rw [ih (by omega)] at hg
      rw [hCg, hCg', hg.unique hg']
end IsGandhiSecond
end PretorsionImageClosed.Statement
