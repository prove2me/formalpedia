-- Prove2me | solution 1 for OddPerfectNumber.vieta_phi5_other_root
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-19T00:52:47.737892+00:00
-- url     : https://prove2.me/submissions/096cbfa6-9bf5-4e7b-8c47-d98689479c68

import Mathlib

theorem solution (x y C : Nat)
    (hx : 0 < x)
    (hy : 0 < y)
    (heq : x ^ 2 + x + y ^ 2 + y + 1 = C * (x * y - 1)) :
    ∃ z : Nat, 0 < z ∧ y + z + 1 = C * x ∧ y * z = x ^ 2 + x + C + 1 ∧
      x ^ 2 + x + z ^ 2 + z + 1 = C * (x * z - 1) := by
  have hxy : 1 < x * y := by
    by_contra h
    push_neg at h
    have hpos : 0 < x * y := mul_pos hx hy
    have heq1 : x * y = 1 := by omega
    have hdx : x ∣ 1 := by
      have h0 : x ∣ x * y := ⟨y, rfl⟩
      rwa [heq1] at h0
    have hdy : y ∣ 1 := by
      have h0 : y ∣ x * y := ⟨x, mul_comm x y⟩
      rwa [heq1] at h0
    have hx1 : x = 1 := Nat.dvd_one.mp hdx
    have hy1 : y = 1 := Nat.dvd_one.mp hdy
    subst hx1
    subst hy1
    simp at heq
  have hsub : x * y - 1 + 1 = x * y := Nat.sub_add_cancel (by omega)
  have hfree : C * (x * y) = x ^ 2 + x + y ^ 2 + y + C + 1 := by
    rw [← hsub, mul_add, mul_one, ← heq]
    ring
  have h_eq : y * (C * x) = y * (y + 1) + (x ^ 2 + x + C + 1) := by
    calc y * (C * x) = C * (x * y) := by ring
    _ = x ^ 2 + x + y ^ 2 + y + C + 1 := hfree
    _ = y * (y + 1) + (x ^ 2 + x + C + 1) := by ring
  have hylt : y * (y + 1) < y * (C * x) := by
    have hpos : 0 < x ^ 2 + x + C + 1 := by omega
    omega
  have hylt2 : y + 1 < C * x := lt_of_mul_lt_mul_left hylt hy.le
  refine ⟨C * x - (y + 1), by omega, by omega, ?_, ?_⟩
  · have hyz_expand : y * (C * x) = y * (y + 1) + y * (C * x - (y + 1)) := by
      have hyz1 : y + (C * x - (y + 1)) + 1 = C * x := by omega
      calc y * (C * x) = y * (y + (C * x - (y + 1)) + 1) := by rw [hyz1]
      _ = y * (y + 1) + y * (C * x - (y + 1)) := by ring
    omega
  · have hCxz : C * x * (C * x - (y + 1)) =
        x ^ 2 + x + (C * x - (y + 1)) ^ 2 + (C * x - (y + 1)) + C + 1 := by
      have e1 : C * x * (C * x - (y + 1)) =
          (C * x - (y + 1)) * (y + (C * x - (y + 1)) + 1) := by
        have hcc : C * x = y + (C * x - (y + 1)) + 1 := by omega
        nth_rewrite 1 [hcc]
        ring
      have e2 : (C * x - (y + 1)) * (y + (C * x - (y + 1)) + 1) =
          y * (C * x - (y + 1)) + (C * x - (y + 1)) ^ 2 + (C * x - (y + 1)) := by
        ring
      have hyz : y * (C * x - (y + 1)) = x ^ 2 + x + C + 1 := by
        have hyz_expand : y * (C * x) = y * (y + 1) + y * (C * x - (y + 1)) := by
          have hyz1 : y + (C * x - (y + 1)) + 1 = C * x := by omega
          calc y * (C * x) = y * (y + (C * x - (y + 1)) + 1) := by rw [hyz1]
          _ = y * (y + 1) + y * (C * x - (y + 1)) := by ring
        omega
      omega
    have h1 : C * (x * (C * x - (y + 1))) = C * x * (C * x - (y + 1)) := by ring
    have h2 : C * (x * (C * x - (y + 1)) - 1) =
        C * (x * (C * x - (y + 1))) - C := by
      rw [mul_tsub, mul_one]
    omega
