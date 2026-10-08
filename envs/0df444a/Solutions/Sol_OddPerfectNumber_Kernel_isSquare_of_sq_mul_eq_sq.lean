-- Prove2me | solution 1 for OddPerfectNumber.Kernel.isSquare_of_sq_mul_eq_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T19:10:31.14379+00:00
-- url     : https://prove2.me/submissions/f2b6b5f5-cecd-4303-b115-f72fb8d0062b

-- Repair of candidate 7357 (2 groups, full report read, END verified).
-- E01 (L25 unsolved): the rw chain applied Finsupp.add_apply only to the outer sum,
--   leaving the inner (d.fact + d.fact) p unapplied. Fix: end the block with
--   simp only [Finsupp.add_apply], which normalizes every unapplied Finsupp sum
--   (skill: a non-finishing rewrite was mistaken for a terminal step).
-- E02 (L39 omega on Even goal): omega's constraint set shows the hpm equation never
--   reached it in linear form (sorry-laden hL/hR from E01 broke the rewrite context),
--   so this is repaired as well by removing the dependence on omega's Even-goal
--   support: exhibit the witness (y-d) + (y-d) via two purely linear omega steps
--   (same shape as the compiling hpos21/hsub steps elsewhere).
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_isSq_iff_even_factorization

theorem solution (d S y : Nat) (hd : d != 0) (hS : S != 0)
    (h : d ^ 2 * S = y ^ 2) : IsSquare S := by
  have hd' : d ≠ 0 := by simpa using hd
  have hS' : S ≠ 0 := by simpa using hS
  have hy : y ≠ 0 := by
    intro hz
    subst hz
    rw [show (0 : Nat) ^ 2 = 0 by norm_num] at h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact (pow_ne_zero 2 hd') h1
    · exact hS' h2
  have hF : (d ^ 2 * S).factorization = (y ^ 2).factorization :=
    congrArg Nat.factorization h
  have hL : ∀ p, (d ^ 2 * S).factorization p =
      d.factorization p + d.factorization p + S.factorization p := by
    intro p
    have e : d ^ 2 * S = (d * d) * S := by ring
    rw [e, Nat.factorization_mul (mul_ne_zero hd' hd') hS',
      Nat.factorization_mul hd' hd']
    simp only [Finsupp.add_apply]
  have hR : ∀ p, (y ^ 2).factorization p =
      y.factorization p + y.factorization p := by
    intro p
    have e : y ^ 2 = y * y := by ring
    rw [e, Nat.factorization_mul hy hy]
    simp only [Finsupp.add_apply]
  have key : ∀ p, Even (S.factorization p) := by
    intro p
    have hpm := congrArg (fun f : Nat →₀ Nat => f p) hF
    rw [hL p, hR p] at hpm
    exact ⟨y.factorization p - d.factorization p, by omega⟩
  have hSq := (OddPerfectNumber.Kernel.isSq_iff_even_factorization hS').mpr key
  obtain ⟨w, hw⟩ := hSq
  exact ⟨w, by rw [← pow_two]; exact hw.symm⟩
