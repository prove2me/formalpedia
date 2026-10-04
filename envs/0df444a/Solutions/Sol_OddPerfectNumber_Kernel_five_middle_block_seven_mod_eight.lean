-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_middle_block_seven_mod_eight
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T13:57:22.735986+00:00
-- url     : https://prove2.me/submissions/bc6333f8-34fe-49ee-8937-e8c244664174

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.five_middle_block_seven_mod_eight
--
-- If `p % 8 = 5` then `(p ^ 2 + p + 1) % 8 = 7`.
--
-- MATHEMATICS.  `p % 8 = 5` is exactly `p = 8 * k + 5`.  Then
-- `p ^ 2 = 64 k^2 + 80 k + 25`, so the block is `64 k^2 + 88 k + 31`, and
-- `64 k^2 + 88 k + 31 = 8 * (8 k^2 + 11 k + 3) + 7`.
--
-- PROOF SHAPE.  As in the accepted `three_val_first_cyclotomic`, `omega` cannot linearise a
-- `pow`, so `p ^ 2` is supplied as an OPAQUE atomic hypothesis proved by `ring` after the
-- substitution.  The subtraction-free identity then leaves `omega` alone.  No truncated
-- `Nat` subtraction and no `Nat.ModEq` appears anywhere.
import Mathlib

namespace OddPerfectNumber
namespace Kernel
namespace Mod8C

theorem solution_aux (p : Nat) (hp8 : p % 8 = 5) :
    (p ^ 2 + p + 1) % 8 = 7 := by
  -- `p % 8 = 5` is exactly `p = 8 * k + 5`.
  obtain ⟨k, hk⟩ : ∃ k : Nat, p = 8 * k + 5 :=
    ⟨p / 8, by omega⟩
  -- `p ^ 2` is opaque to `omega`, so it is supplied after the substitution by `ring`.
  have hsq : p ^ 2 = 64 * (k * k) + 80 * k + 25 := by
    rw [hk]
    ring
  have hpos : 1 <= p := by omega
  -- `64 k^2 + 88 k + 31 = 8 * (8 k^2 + 11 k + 3) + 7`, so the remainder is `7`.
  have hform : p ^ 2 + p + 1 = 8 * (8 * (k * k) + 11 * k + 3) + 7 := by omega
  rw [hform]
  omega

end Mod8C
end Kernel
end OddPerfectNumber

open OddPerfectNumber
open OddPerfectNumber.Kernel

theorem solution (p : Nat) (hp8 : p % 8 = 5) :
    (p ^ 2 + p + 1) % 8 = 7 :=
  OddPerfectNumber.Kernel.Mod8C.solution_aux p hp8
