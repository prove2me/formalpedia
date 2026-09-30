-- Prove2me | solution 1 for TranscendenceTheory.three_step_minimal_prime_selection
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-20T20:09:23.51299+00:00
-- url     : https://prove2.me/submissions/183fc427-389c-4afe-bf94-f7648aaba8bd

import Mathlib.RingTheory.Ideal.Height
import Mathlib.Tactic

namespace TranscendenceTheory


end TranscendenceTheory

open TranscendenceTheory

theorem solution
    (R : Type*) [CommRing R] (J : Fin 4 → Ideal R) (hJ : Monotone J)
    (q : Ideal R) [q.IsPrime]
    (hterminal : J 3 ≤ q) (hlower : (2 : ℕ∞) ≤ (J 0).height)
    (hupper : q.height ≤ (4 : ℕ∞)) :
    ∃ (i : Fin 3) (p : Ideal R), p ≤ q ∧
      p ∈ (J i.castSucc).minimalPrimes ∧ p ∈ (J i.succ).minimalPrimes := by
  classical
  obtain ⟨p3, h3, h3q⟩ := Ideal.exists_minimalPrimes_le hterminal
  let : p3.IsPrime := h3.isPrime
  obtain ⟨p2, h2, h23⟩ := Ideal.exists_minimalPrimes_le
    ((hJ (show (2 : Fin 4) ≤ 3 by decide)).trans h3.le)
  let : p2.IsPrime := h2.isPrime
  obtain ⟨p1, h1, h12⟩ := Ideal.exists_minimalPrimes_le
    ((hJ (show (1 : Fin 4) ≤ 2 by decide)).trans h2.le)
  let : p1.IsPrime := h1.isPrime
  obtain ⟨p0, h0, h01⟩ := Ideal.exists_minimalPrimes_le
    ((hJ (show (0 : Fin 4) ≤ 1 by decide)).trans h1.le)
  let : p0.IsPrime := h0.isPrime
  by_cases he01 : p0 = p1
  · exact ⟨0, p0, h01.trans (h12.trans (h23.trans h3q)), h0, he01 ▸ h1⟩
  by_cases he12 : p1 = p2
  · exact ⟨1, p1, h12.trans (h23.trans h3q), h1, he12 ▸ h2⟩
  by_cases he23 : p2 = p3
  · exact ⟨2, p2, h23.trans h3q, h2, he23 ▸ h3⟩
  have h01' := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne h01 he01)
  have h12' := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne h12 he12)
  have h23' := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne h23 he23)
  have hlow : (2 : ℕ∞) ≤ p0.height := hlower.trans (Ideal.height_mono h0.le)
  have hbad : (5 : ℕ∞) ≤ (4 : ℕ∞) := calc
    (5 : ℕ∞) = 2 + 1 + 1 + 1 := by norm_num
    _ ≤ p0.height + 1 + 1 + 1 := by gcongr
    _ ≤ p1.height + 1 + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using
        add_le_add_right (add_le_add_right h01' 1) 1
    _ ≤ p2.height + 1 := by
      simpa [add_comm, add_left_comm, add_assoc] using add_le_add_right h12' 1
    _ ≤ p3.height := h23'
    _ ≤ q.height := Ideal.height_mono h3q
    _ ≤ 4 := hupper
  norm_num at hbad
