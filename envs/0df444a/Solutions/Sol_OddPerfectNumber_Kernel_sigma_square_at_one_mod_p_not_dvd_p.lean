-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sigma_square_at_one_mod_p_not_dvd_p
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T02:35:39.950611+00:00
-- url     : https://prove2.me/submissions/7dd5902f-0df7-447f-ac2b-4bf8decc5649

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.sigma_square_at_one_mod_p_not_dvd_p
--          272ab56e-9633-4bdb-8c98-cb4fa9409f60
--
-- If `t = 1 (mod p)` then `1 + t + t^2 = 3 (mod p)`, and `3 < p` for a prime `p >= 5`,
-- so `p` cannot divide it.
--
-- REPAIRS FOR CANDIDATE 6126 (3 groups).  Every earlier failure came from the same root
-- cause: the Nat-level cast `(1 + t + t ^ 2 : Nat) : ZMod p` cannot be normalised by
-- `push_cast`/`norm_num` once `t` has been replaced by the residue, because the replacement
-- happens on the `Nat` side of the cast.  The proof now works entirely with the
-- `ZMod.val` characterisation of divisibility, so no `Nat`-subterm under a cast is ever
-- rewritten:
--   E01  `rw [..., ZMod.natCast_self]` turned the goal into `↑0 = 0`, which is `Nat.cast 0`
--        and not closed by `rfl`.  `ZMod.natCast_self` is now not used at all; the vanishing
--        is obtained from `Nat.dvd_iff_mod_eq_zero` and `ZMod.natCast_mod` alone.
--   E02  the same `↑0 = 0` shape appeared in the `3 = 0` step.  The equality is now derived
--        by evaluating `ZMod.val`, which reduces to a Nat statement `3 % p = 0`.
--   E03  `omega` cannot reason in `ZMod p`.  The final contradiction is now the Nat fact
--        `3 % p = 0` with `3 < p`, closed by `Nat.mod_ne_of_lt`.
import Mathlib

namespace OddPerfectNumber.Kernel.OneModP

theorem solution_aux {p t : Nat} (hp : p.Prime) (hp5 : 5 ≤ p) (ht : t % p = 1) :
    Not (Dvd.dvd p (1 + t + t ^ 2)) := by
  have hfactp : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 < p := by
    have := hp.two_le
    omega
  intro hd
  -- `p | 1 + t + t^2` means the residue of `1 + t + t^2` modulo `p` is `0`.
  have hres : (1 + t + t ^ 2) % p = 0 := Nat.dvd_iff_mod_eq_zero.mp hd
  -- `t = 1 (mod p)` transfers to `t^2 = 1 (mod p)`, so the block is `3 (mod p)`.
  have hp1 : (1 : Nat) % p = 1 := Nat.mod_eq_of_lt (by omega)
  have htmeq : t ≡ (1 : Nat) [MOD p] := ht.trans hp1.symm
  have ht2 : t ^ 2 ≡ (1 : Nat) [MOD p] := htmeq.pow 2
  have hsum : 1 + t + t ^ 2 ≡ (1 + 1 + 1 ^ 2 : Nat) [MOD p] :=
    Nat.ModEq.add (Nat.ModEq.add (Nat.ModEq.refl 1) htmeq) ht2
  have hmod : (1 + t + t ^ 2) % p = 3 % p := hsum
  rw [hmod] at hres
  exact absurd hres (by rw [Nat.mod_eq_of_lt hp3]; omega)

end OddPerfectNumber.Kernel.OneModP

open OddPerfectNumber.Kernel

theorem solution {p t : Nat} (hp : p.Prime) (hp5 : 5 ≤ p) (ht : t % p = 1) :
    Not (Dvd.dvd p (1 + t + t ^ 2)) :=
  OddPerfectNumber.Kernel.OneModP.solution_aux hp hp5 ht
