-- Prove2me | solution 2 for Richstein2001.segmented_sieve_block_witnesses_final_block
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:38:20.234456+00:00
-- url     : https://prove2.me/submissions/a00f0135-8256-445e-98b4-77a117381e7d

import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity
import Mathlib.Tactic
import Mathlib.Tactic.ReduceModChar
import Mathlib.NumberTheory.LucasPrimality

theorem solution (b : ℕ) (hb : b < 400000001) (hfinal : b = 400000000) :
    ∀ n ∈ ((Finset.Icc (max 4 (b * 1000000))
      (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1))).filter (fun n => Even n)),
      ∃ p ∈ ((Finset.Icc 2 5569).filter Nat.Prime),
        ∃ q ∈ GoldbachSieve.survivors (b * 1000000 - 5569)
          (min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1)) 20000000,
          n = p + q := by
  subst b
  intro n hn
  have hnIcc := (Finset.mem_filter.mp hn).1
  have hnIcc' : 400000000000000 ≤ n ∧ n ≤ 400000000000000 := by
    norm_num [Finset.mem_Icc] at hnIcc
    omega
  have hnval : n = 400000000000000 := by omega
  subst n
  refine ⟨3, ?_, 399999999999997, ?_, by norm_num⟩
  · norm_num
  · change 399999999999997 ∈
      ((Finset.Icc (max 2 (400000000000000 - 5569)) 400000000000000).filter
        (fun q =>
          (((Finset.Icc 2 20000000).filter Nat.Prime).filter
            (fun r => r ∣ q ∧ r ≠ q)).card = 0))
    apply Finset.mem_filter.mpr
    constructor
    · norm_num
    · have hq : Nat.Prime 399999999999997 := by
        apply lucas_primality 399999999999997 (2 : ZMod 399999999999997)
        · reduce_mod_char
        · intro r hr hdiv
          have hfac : 399999999999997 - 1 =
              2 ^ 2 * (3 ^ 2 * (11 * (239 * (4649 * 909091)))) := by norm_num
          rw [hfac] at hdiv
          rcases (Nat.Prime.dvd_mul hr).mp hdiv with h2 | hrest
          · have heq : r = 2 := by
              apply (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp
              exact hr.dvd_of_dvd_pow h2
            subst r
            reduce_mod_char
            change ¬ (((399999999999996 : Nat) : ZMod 399999999999997) =
              ((1 : Nat) : ZMod 399999999999997))
            rw [ZMod.natCast_eq_natCast_iff']
            norm_num
          · rcases (Nat.Prime.dvd_mul hr).mp hrest with h3 | hrest
            · have heq : r = 3 := by
                apply (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).mp
                exact hr.dvd_of_dvd_pow h3
              subst r
              reduce_mod_char
              change ¬ (((271776851199801 : Nat) : ZMod 399999999999997) =
                ((1 : Nat) : ZMod 399999999999997))
              rw [ZMod.natCast_eq_natCast_iff']
              norm_num
            · rcases (Nat.Prime.dvd_mul hr).mp hrest with h11 | hrest
              · have hp : Nat.Prime 11 := by norm_num
                have heq : r = 11 := (Nat.prime_dvd_prime_iff_eq hr hp).mp h11
                subst r
                reduce_mod_char
                change ¬ (((157776712886010 : Nat) : ZMod 399999999999997) =
                  ((1 : Nat) : ZMod 399999999999997))
                rw [ZMod.natCast_eq_natCast_iff']
                norm_num
              · rcases (Nat.Prime.dvd_mul hr).mp hrest with h239 | hrest
                · have hp : Nat.Prime 239 := by norm_num
                  have heq : r = 239 := (Nat.prime_dvd_prime_iff_eq hr hp).mp h239
                  subst r
                  reduce_mod_char
                  change ¬ (((3242822643068 : Nat) : ZMod 399999999999997) =
                    ((1 : Nat) : ZMod 399999999999997))
                  rw [ZMod.natCast_eq_natCast_iff']
                  norm_num
                · rcases (Nat.Prime.dvd_mul hr).mp hrest with h4649 | h909091
                  · have hp : Nat.Prime 4649 := by norm_num
                    have heq : r = 4649 := (Nat.prime_dvd_prime_iff_eq hr hp).mp h4649
                    subst r
                    reduce_mod_char
                    change ¬ (((14040663321953 : Nat) : ZMod 399999999999997) =
                      ((1 : Nat) : ZMod 399999999999997))
                    rw [ZMod.natCast_eq_natCast_iff']
                    norm_num
                  · have hp : Nat.Prime 909091 := by norm_num
                    have heq : r = 909091 := (Nat.prime_dvd_prime_iff_eq hr hp).mp h909091
                    subst r
                    norm_num
                    reduce_mod_char
                    change ¬ (((301265643873373 : Nat) : ZMod 399999999999997) =
                      ((1 : Nat) : ZMod 399999999999997))
                    rw [ZMod.natCast_eq_natCast_iff']
                    norm_num
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro r hr hbad
      rcases hbad with ⟨hdiv, hneq⟩
      rcases Finset.mem_filter.mp hr with ⟨hrIcc, _⟩
      have hrIcc' := Finset.mem_Icc.mp hrIcc
      have heq : r = 399999999999997 :=
        (Nat.dvd_prime_two_le hq hrIcc'.1).mp hdiv
      exact hneq heq
