-- Prove2me | solution 1 for OddPerfectNumber.four_support_ordered
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-13T15:50:12.16847+00:00
-- url     : https://prove2.me/submissions/97416290-4b0c-4ab3-acbf-d25055b0ce84

import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Finset.Sort

theorem solution (m : Nat)
    (hcard : m.primeFactors.card = 4) :
    ∃ q1 q2 q3 q4 : Nat,
      q1.Prime ∧ q2.Prime ∧ q3.Prime ∧ q4.Prime ∧
      q1 < q2 ∧ q2 < q3 ∧ q3 < q4 ∧
      m.primeFactors = {q1, q2, q3, q4} := by
  have hlen : (m.primeFactors.sort (· ≤ ·)).length = 4 := by
    rw [Finset.length_sort, hcard]
  obtain ⟨q1, q2, q3, q4, hlist⟩ := List.length_eq_four.mp hlen
  have hpair : (m.primeFactors.sort (· ≤ ·)).Pairwise (· < ·) :=
    (Finset.sortedLT_sort m.primeFactors).pairwise
  rw [hlist] at hpair
  have h12 : q1 < q2 := by
    exact (List.pairwise_cons.mp hpair).1 q2 (by simp)
  have htail : (q2 :: q3 :: q4 :: []).Pairwise (· < ·) :=
    (List.pairwise_cons.mp hpair).2
  have h23 : q2 < q3 := by
    exact (List.pairwise_cons.mp htail).1 q3 (by simp)
  have htail' : (q3 :: q4 :: []).Pairwise (· < ·) :=
    (List.pairwise_cons.mp htail).2
  have h34 : q3 < q4 := by
    exact (List.pairwise_cons.mp htail').1 q4 (by simp)
  have hset : (m.primeFactors.sort (· ≤ ·)).toFinset = m.primeFactors :=
    Finset.sort_toFinset _ _
  rw [hlist] at hset
  have hq1mem : q1 ∈ m.primeFactors := by
    rw [← hset]
    simp
  have hq2mem : q2 ∈ m.primeFactors := by
    rw [← hset]
    simp
  have hq3mem : q3 ∈ m.primeFactors := by
    rw [← hset]
    simp
  have hq4mem : q4 ∈ m.primeFactors := by
    rw [← hset]
    simp
  have hsupport : m.primeFactors = {q1, q2, q3, q4} := by
    simpa using hset.symm
  exact ⟨q1, q2, q3, q4,
    Nat.prime_of_mem_primeFactors hq1mem,
    Nat.prime_of_mem_primeFactors hq2mem,
    Nat.prime_of_mem_primeFactors hq3mem,
    Nat.prime_of_mem_primeFactors hq4mem,
    h12, h23, h34, hsupport⟩
