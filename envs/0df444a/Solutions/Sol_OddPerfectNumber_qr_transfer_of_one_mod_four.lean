-- Prove2me | solution 1 for OddPerfectNumber.qr_transfer_of_one_mod_four
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T11:24:08.11461+00:00
-- url     : https://prove2.me/submissions/eda07cfa-c554-495b-a786-91f1b7edff56

import Mathlib

-- Sign-free reciprocity: reflect IsSquare across the two moduli via
-- legendreSym, discharging nonvanishing through primality.
theorem solution {p q : Nat} (hp : p.Prime) (hq : q.Prime)
    (hp4 : p % 4 = 1) (hq2 : q ≠ 2) (hqp : q ≠ p)
    (hsq : IsSquare (q : ZMod p)) : IsSquare (p : ZMod q) := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact q.Prime := ⟨hq⟩
  have hpq0 : (q : ZMod p) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff] at h0
    rcases (Nat.dvd_prime hq).mp h0 with h1 | h1
    · exact hp.ne_one h1
    · exact hqp h1.symm
  have hqp0 : (p : ZMod q) ≠ 0 := by
    intro h0
    rw [CharP.cast_eq_zero_iff] at h0
    rcases (Nat.dvd_prime hp).mp h0 with h1 | h1
    · exact hq.ne_one h1
    · exact hqp h1
  -- NOTE (remote CE 544fd548): eq_one_iff' takes an explicit Nat argument
  -- (modulus/numerator) before the nonvanishing proof; leave it inferred.
  rw [← legendreSym.eq_one_iff' _ hqp0,
    legendreSym.quadratic_reciprocity_one_mod_four hp4 hq2]
  exact (legendreSym.eq_one_iff' _ hpq0).mpr hsq
