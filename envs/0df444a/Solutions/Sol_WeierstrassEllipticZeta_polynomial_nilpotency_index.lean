-- Prove2me | solution 1 for WeierstrassEllipticZeta.polynomial_nilpotency_index
-- status  : ACCEPTED   (prove)
-- author  : @tomasz
-- created : 2026-09-11T04:52:02.763053+00:00
-- url     : https://prove2.me/submissions/d794c9f9-5a32-4783-9a30-47e1c3093cfb

import Theorems.Thm_WeierstrassEllipticZeta_polynomial_nilpotent_root_order
import Mathlib.Algebra.Order.Floor.Div



theorem solution
    (K A : Type*) [Field K] [CommRing A]
    (φ : K →+* A) (x : A) (z : K) (d : ℕ) (hx : (x - φ z) ^ d = 0)
    (q : Polynomial K) (hq : q ≠ 0) :
    let n := nilpotencyClass (x - φ z)
    let r := q.rootMultiplicity z
    (∀ k : ℕ, (q.eval₂ φ x) ^ k = 0 ↔ n ≤ r * k) ∧
      (0 < r → IsNilpotent (q.eval₂ φ x) ∧
        nilpotencyClass (q.eval₂ φ x) = (n + r - 1) / r) := by
  let n := nilpotencyClass (x - φ z)
  let r := q.rootMultiplicity z
  have hn (k : ℕ) : (x - φ z) ^ k = 0 ↔ n ≤ k :=
    ⟨fun h => Nat.sInf_le h,
      fun h => pow_eq_zero_of_le h (pow_nilpotencyClass ⟨d, hx⟩)⟩
  obtain ⟨u, hu, hpower, hbound⟩ :=
    WeierstrassEllipticZeta.polynomial_nilpotent_root_order K A φ x z d hx q hq
  have hiff (k : ℕ) : (q.eval₂ φ x) ^ k = 0 ↔ n ≤ r * k :=
    (hpower k).trans (hn _)
  refine ⟨hiff, ?_⟩
  intro hr
  let N := (n + r - 1) / r
  have hN (k : ℕ) : N ≤ k ↔ n ≤ r * k := ceilDiv_le_iff_le_mul hr
  have hzero : (q.eval₂ φ x) ^ N = 0 := (hiff N).mpr ((hN N).mp le_rfl)
  have hnil : IsNilpotent (q.eval₂ φ x) := ⟨N, hzero⟩
  refine ⟨hnil, le_antisymm (Nat.sInf_le hzero) ?_⟩
  exact (hN _).mpr ((hiff _).mp (pow_nilpotencyClass hnil))

