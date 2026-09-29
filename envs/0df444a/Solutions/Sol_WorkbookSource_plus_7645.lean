-- Prove2me | solution 1 for WorkbookSource.plus_7645
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T14:47:28.008764+00:00
-- url     : https://prove2.me/submissions/c505b699-007f-47b4-9ac8-862f9725eb1a

/- Source: InternLM Lean-Workbook lean_workbook_plus_7645, Apache-2.0.
https://huggingface.co/datasets/internlm/Lean-Workbook/blob/main/lean_workbook.json -/
import Mathlib
open Nat Real
set_option autoImplicit false
set_option maxHeartbeats 400000
theorem solution (n : ℕ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hn : n = p*q) : {d | d ∣ n} = {1, p, q, p*q} := by
  ext a
  simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [hn]
  simp only [Nat.isUnit_iff, Nat.dvd_mul, Nat.dvd_prime hp, Nat.dvd_prime hq]
  aesop

example : (∀ (n : ℕ) (p q : ℕ) (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (hn : n = p*q), {d | d ∣ n} = {1, p, q, p*q}) := @solution
#print axioms solution
