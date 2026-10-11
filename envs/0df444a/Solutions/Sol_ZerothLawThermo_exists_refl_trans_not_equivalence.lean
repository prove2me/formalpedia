-- Prove2me | solution 1 for ZerothLawThermo.exists_refl_trans_not_equivalence
-- status  : ACCEPTED   (prove)
-- author  : @arexychen
-- created : 2026-10-11T03:42:51.764431+00:00
-- url     : https://prove2.me/submissions/c0834f3a-7b7c-404d-8649-bcbcb0977d0d

import Definitions.Def_ZerothLawThermo_Defs
import Mathlib

open ZerothLawThermo

theorem solution :
    ∃ (S : Type) (R : S → S → Prop),
      (∀ A : S, R A A) ∧ (∀ A B C : S, R A B → R B C → R A C) ∧ ¬ Equivalence R := by
  refine ⟨ℕ, (· ≤ ·), fun _ => le_rfl, fun _ _ _ => le_trans, ?_⟩
  intro h
  have hf : (1 : ℕ) ≤ 0 := h.symm (Nat.zero_le 1)
  omega
