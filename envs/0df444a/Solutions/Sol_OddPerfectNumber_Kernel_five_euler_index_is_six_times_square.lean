-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_euler_index_is_six_times_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T09:52:13.352982+00:00
-- url     : https://prove2.me/submissions/f3ff8c81-cf3a-4cd5-8c9b-8e4835516840

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.five_euler_index_is_six_times_square
--          d1cc5c3a-5d27-4d4e-aa56-f2342521c0d9
--
-- The algebraic endgame of the 3-adic analysis of the k=5 Dris branch.
--
-- Write `B = (p+1)/2` and `a = v3(p+1)`.  In the branch that matters `a` is ODD, so
-- `a = 2k+1`, and the residual forces the 3-free part of `B` to be a square, i.e.
-- `B = 3^(2k+1) * v^2`.  Then
--
--     3^(2k+1) = 3 * (3^k)^2        (pow_add, then pow_mul, then ring)
--     p + 1     = 2 * B = 6 * (3^k * v)^2
--
-- so `u = 3^k * v`.  Note the exponent `2k+1` is exactly what leaves ONE factor of `3`
-- outside the square; that is why the conclusion is `6 * u^2` and not a plain square.
--
-- The supplied reference candidate `lean/05_shape_from_square_part.lean` uses exactly this
-- route; the `rw [mul_comm 2 k, pow_mul]` step needs `3^(2k+1) = 3^(2k) * 3^1` first, which
-- is `pow_add`.
import Mathlib

namespace OddPerfectNumber
namespace Kernel
namespace SixSq

theorem aux (p B k v : Nat)
    (hhalf : p + 1 = 2 * B)
    (hB : B = 3 ^ (2 * k + 1) * v ^ 2) :
    exists u : Nat, p + 1 = 6 * u ^ 2 := by
  -- `3^(2k+1) = 3^(2k) * 3^1 = (3^k)^2 * 3`.
  -- Candidate 6282 left the goal `9 ^ k * 3 = 3 ^ (k * 2) * 3`: `pow_mul` had rewritten
  -- `(3^k)^2` as `3^(k*2)`, and `ring` cannot reassociate the EXPONENT `k * 2` into `2 * k`.
  -- `Nat.mul_comm k 2` fixes the exponent BEFORE `ring`, which is the shape of the supplied
  -- reference `lean/05_shape_from_square_part.lean`.
  have he : 3 ^ (2 * k + 1) = 3 * (3 ^ k) ^ 2 := by
    rw [show 2 * k + 1 = 2 * k + 1 by rfl, pow_add, mul_comm 2 k, pow_mul]
    ring
  refine ⟨3 ^ k * v, ?_⟩
  calc
    p + 1 = 2 * B := hhalf
    _ = 2 * (3 ^ (2 * k + 1) * v ^ 2) := by rw [hB]
    _ = 6 * (3 ^ k * v) ^ 2 := by rw [he]; ring

end SixSq
end Kernel
end OddPerfectNumber

open OddPerfectNumber.Kernel

theorem solution (p B k v : Nat)
    (hhalf : p + 1 = 2 * B)
    (hB : B = 3 ^ (2 * k + 1) * v ^ 2) :
    exists u : Nat, p + 1 = 6 * u ^ 2 :=
  OddPerfectNumber.Kernel.SixSq.aux p B k v hhalf hB
