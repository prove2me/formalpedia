-- Prove2me | solution 1 for SmaleNinth.elim_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @Zexuan Liu
-- created : 2026-09-08T02:48:18.937515+00:00
-- url     : https://prove2.me/submissions/5a25043c-125c-4a3c-876c-47c9c182d68a

import Definitions.Def_SmaleNinth_ElimIdx
import Mathlib.Tactic

/-!
# Size of the Fourier–Motzkin eliminated system

One step sends a count `N` to `N + N * N`, and `N + N * N + 1 ≤ (N + 1) ^ 2`, so
the shifted count `# + 1` squares at each step exactly as the exponent doubles.
-/

open SmaleNinth

lemma card_bound_aux : ∀ (n : ℕ) (ι : Type) (h : Fintype ι),
    @Fintype.card (ElimIdx n ι) (elimIdxFintypeAux n ι h) + 1
      ≤ (@Fintype.card ι h + 1) ^ (2 ^ n) := by
  intro n
  induction n with
  | zero =>
    intro ι h
    simp only [ElimIdx, elimIdxFintypeAux, pow_zero, pow_one]
    exact le_rfl
  | succ n ih =>
    intro ι h
    have key := ih (ι ⊕ ι × ι) (@instFintypeSum _ _ h (@instFintypeProd _ _ h h))
    set N := @Fintype.card ι h with hN
    have hcard : @Fintype.card (ι ⊕ ι × ι) (@instFintypeSum _ _ h (@instFintypeProd _ _ h h))
        = N + N * N := by
      simp [Fintype.card_sum, Fintype.card_prod, hN]
    rw [hcard] at key
    calc @Fintype.card (ElimIdx (n + 1) ι) (elimIdxFintypeAux (n + 1) ι h) + 1
        ≤ (N + N * N + 1) ^ (2 ^ n) := key
      _ ≤ ((N + 1) ^ 2) ^ (2 ^ n) := by
          refine Nat.pow_le_pow_left ?_ _
          nlinarith
      _ = (N + 1) ^ (2 ^ (n + 1)) := by
          rw [← pow_mul]
          congr 1
          ring

theorem solution (n m : ℕ) :
    Fintype.card (SmaleNinth.ElimIdx n (Fin m)) + 1 ≤ (m + 1) ^ (2 ^ n) := by
  have := card_bound_aux n (Fin m) (Fin.fintype m)
  simpa using this
