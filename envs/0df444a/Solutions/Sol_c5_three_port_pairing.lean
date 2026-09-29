-- Prove2me | solution 1 for c5_three_port_pairing
-- status  : ACCEPTED   (prove)
-- author  : @hao jia
-- created : 2026-09-25T21:10:58.48982+00:00
-- url     : https://prove2.me/submissions/150ae878-6eb7-4e40-9936-9de06a8966b8

import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.FinCases

theorem solution :
    ∀ (u v r : Fin 5),
      u ≠ v →
      ¬ ((u.val + 1) % 5 = v.val ∨ (v.val + 1) % 5 = u.val) →
      let T : Finset (Fin 5) := (Finset.univ.erase u).erase v
      r ∈ T →
      ∃ (a b c d : Fin 5),
        a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
        ((a.val + 1) % 5 = b.val ∨ (b.val + 1) % 5 = a.val) ∧
        ((c.val + 1) % 5 = d.val ∨ (d.val + 1) % 5 = c.val) ∧
        ({a, b, c, d} : Finset (Fin 5)) = Finset.univ.erase r ∧
        ((a ∈ T ∧ b ∉ T) ∨ (a ∉ T ∧ b ∈ T)) ∧
        ((c ∈ T ∧ d ∉ T) ∨ (c ∉ T ∧ d ∈ T)) := by
  intro u v r huv hnonadj hr
  fin_cases u <;> fin_cases v <;> fin_cases r <;>
    simp_all <;> decide
