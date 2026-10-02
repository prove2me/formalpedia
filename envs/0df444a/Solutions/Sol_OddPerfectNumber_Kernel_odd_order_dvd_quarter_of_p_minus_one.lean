-- Prove2me | solution 1 for OddPerfectNumber.Kernel.odd_order_dvd_quarter_of_p_minus_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-01T14:54:21.059325+00:00
-- url     : https://prove2.me/submissions/bc928e68-13a6-47a0-ad32-cca9ef8adb7b

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
-- Target: OddPerfectNumber.Kernel.odd_order_dvd_quarter_of_p_minus_one
--          08fe6da2-1ba0-4692-b142-e9c52d0cdc9a
--
-- An odd multiplicative order divides a quarter of p - 1.
--
-- This is the CORRECTED form of the Disproved target
-- `odd_order_dvd_half_of_p_minus_one` (e016fbd8).  That target carried no
-- oddness hypothesis, so even orders were in scope and genuinely refuted it
-- (p=5, t=2: order 4 does not divide 2; p=13, t=5: order 4 does not divide 6;
-- p=17, t=3: order 16 does not divide 8).  Adding `Odd (orderOf ..)` repairs
-- the defect and the conclusion strengthens from (p-1)/2 to (p-1)/4.
--
-- Arithmetic of the proof.  The order divides p-1, the order is odd so it is
-- coprime to 2 and therefore to 4, and `p % 4 = 1` says p-1 is four times
-- (p-1)/4; the coprime factor 4 then cancels.  No case split and no
-- computation is needed.
--
-- Consequence for the k=5 residual.  Any local sigma source t of the Euler
-- prime p satisfies `p ∣ 1 + t + ... + t^(2e)`, so the accepted
-- `geom_sum_dvd_implies_order_dvd` (d9c2c20a) gives `orderOf (t : ZMod p) ∣ 2e+1`
-- and the order is odd; this child then forces `orderOf .. ∣ (p-1)/4`, i.e. t is
-- a FOURTH power modulo p -- strictly stronger than the quadratic-residue
-- condition obtained from (p-1)/2 alone.
--
-- Diagnostic notes.  Declaration spellings are taken from accepted mission
-- sources rather than guessed: `ZMod.orderOf_dvd_card_sub_one` with the
-- hypothesis `(t : ZMod p) ≠ 0` (`solution_even_order_41_mod_89.lean:12`), and
-- `Nat.coprime_pow_right_iff` for lifting coprimality with 2 to a power
-- (same file, line 18).  The `Fact (Nat.Prime p)` instance is what lets
-- `ZMod.orderOf_dvd_card_sub_one` produce `orderOf .. ∣ p - 1`.  Turning
-- `p ∤ t` into `(t : ZMod p) ≠ 0` uses `CharP.cast_eq_zero_iff`, the spelling
-- accepted in `solution_even_order_odd_geom_sum_not_dvd.lean:17`.
import Mathlib

namespace OddPerfectNumber.Kernel
namespace OddQuarter

theorem solution_aux {p t : Nat} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hpt : Not (Dvd.dvd p t))
    (hodd : Odd (orderOf (t : ZMod p))) :
    Dvd.dvd (orderOf (t : ZMod p)) ((p - 1) / 4) := by
  have hpos : 0 < p := hp.pos
  letI : Fact (Nat.Prime p) := ⟨hp⟩
  letI : NeZero p := ⟨hpos.ne'⟩
  -- `(t : ZMod p) = 0` says `t % p = 0` by the plain cast characterisation
  -- `ZMod.natCast_eq_natCast_iff' (a b c) : (a : ZMod c) = (b : ZMod c) <-> a % c = b % c`.
  -- It needs NO primality instance and returns an ordinary EQUATION, so the whole
  -- `Nat.ModEq` bridge is unnecessary: `0 % p = 0` is closed by `simp` and
  -- `t % p = 0` is exactly `p | t`.
  --
  -- This replaces the `ModEq` chain of candidates 5461/5498/5526/5606/5619/5636,
  -- whose failures were:
  --   5461/5498 `failed to synthesize CharP (ZMod p) t` -- `CharP` is indexed by
  --     the CHARACTER (`CharP (ZMod p) p`), not by the value `t`.
  --   5526 `(ZMod.natCast_eq_natCast_iff t 0 p).mp hcast : t ≡ 0 [MOD p]` -- the
  --     sibling declaration returns a CONGRUENCE, needing `Nat.modEq_iff_dvd'`
  --     and its `1 <= b` side condition, which `b = 0` cannot supply (5636 then
  --     reported `Actual type: ?m.101 | p - 2 / Expected type: p | t - p`).
  --   5606 `Nat.ModEq.of_dvd : a ≡ b [MOD c] -> a ≡ b [MOD k]` for `k | c` -- it
  --     REFINES a modulus and so is not the bridge.
  --   5619 `Unknown constant Nat.ModEq.zero_iff_dvd.mpr`.
  -- The accepted corpus uses `ZMod.natCast_eq_natCast_iff'` with a NUMERAL modulus
  -- (`solution_even_orders_mod_157_q3_twentythree.lean:25`); using the same
  -- declaration with the VARIABLE modulus is what removes the `Fact` dependency.
  have hne0 : (t : ZMod p) ≠ 0 := by
    intro hzero
    have hcast : (((t : Nat) : ZMod p) = ((0 : Nat) : ZMod p)) := by
      push_cast
      exact hzero
    have hmod : t % p = 0 := (ZMod.natCast_eq_natCast_iff' t 0 p).mp hcast
    exact hpt (Nat.dvd_of_mod_eq_zero hmod)

  -- Fermat: `t ^ (p - 1) = 1` in `ZMod p`, so `orderOf | p - 1`.
  have hpow : (t : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hne0
  have hcard : orderOf (t : ZMod p) ∣ p - 1 := orderOf_dvd_of_pow_eq_one hpow
  have hfour : p - 1 = 4 * ((p - 1) / 4) := by
    have h1 : p % 4 = 1 := hp4
    have hlt : 1 < 4 := by norm_num
    omega
  have hcop2 : Nat.Coprime (orderOf (t : ZMod p)) 2 := hodd.coprime_two_right
  have hcop4 : Nat.Coprime (orderOf (t : ZMod p)) (2 ^ 2) :=
    (Nat.coprime_pow_right_iff (show 0 < 2 by norm_num)
      (orderOf (t : ZMod p)) 2).mpr hcop2
  have hhdvd : Dvd.dvd (orderOf (t : ZMod p)) (4 * ((p - 1) / 4)) := by
    rw [← hfour]
    exact hcard
  have hres : Dvd.dvd (orderOf (t : ZMod p)) ((p - 1) / 4) :=
    (hcop4.dvd_mul_left).mp hhdvd
  simpa using hres

end OddQuarter
end OddPerfectNumber.Kernel

open OddPerfectNumber.Kernel

theorem solution {p t : Nat} (hp : p.Prime)
    (hp4 : p % 4 = 1) (hpt : Not (Dvd.dvd p t))
    (hodd : Odd (orderOf (t : ZMod p))) :
    Dvd.dvd (orderOf (t : ZMod p)) ((p - 1) / 4) :=
  OddPerfectNumber.Kernel.OddQuarter.solution_aux hp hp4 hpt hodd
