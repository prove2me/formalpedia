-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_source_location_disjunction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T14:12:06.073103+00:00
-- url     : https://prove2.me/submissions/1029dc63-67d2-40c4-9f5f-95bdb1312285

-- Target: OddPerfectNumber.Kernel.five_two_prime_source_location_disjunction (1312beaa).
-- Round-7 repair.  CE 7276 and CE 7277 reported the SAME two groups, and the CE text settles the
-- peel orientation EMPIRICALLY, which two earlier notes in this workstream had backwards.
--
-- CE 7276 L32 / CE 7277 L35, verbatim:
--   The argument `ha` has type `t | a * b * c * d` but is expected to have type `t | a`
--   in the application `Or.inl ha`
-- So applying `ht.dvd_mul` to `h : t | (a * b * c * d) * e` produces the LEFT disjunct
-- `t | a * b * c * d`, NOT `t | a`.  That means the FIRST application peels the LEFT factor of the
-- OUTERMOST product, namely `a * b * c * d` -- the four-fold block -- and only then does the next
-- application split that block.  My previous code assumed each application peels a single letter.
--
-- CE 7276 L33 / CE 7277 L36, verbatim:
--   The argument `hrest` has type `t | e` but is expected to have type `t | ?m * ?m`
--   in the application `(Nat.Prime.dvd_mul ht).mp hrest`
-- So the SECOND disjunct is `t | e`, confirming the outer split is `((a*b)*c)*d \/ e`.
--
-- CORRECT PEEL ORDER, read off the diagnostics: d, then c, then b, then a, with `e` as the
-- fallback leaf of the outermost split.
import Mathlib

theorem solution (t a b c d e : Nat) (ht : t.Prime)
    (h : Dvd.dvd t (a * b * c * d * e)) :
    Dvd.dvd t a \/ Dvd.dvd t b \/ Dvd.dvd t c \/ Dvd.dvd t d \/ Dvd.dvd t e := by
  -- Outermost split of `(((a*b)*c)*d) * e`: left block `((a*b)*c)*d`, or `e`.
  rcases (ht.dvd_mul).mp h with h4 | he
  · -- h4 : t | ((a*b)*c)*d
    rcases (ht.dvd_mul).mp h4 with h3 | hd
    · -- h3 : t | (a*b)*c
      rcases (ht.dvd_mul).mp h3 with h2 | hc
      · -- h2 : t | a*b
        rcases (ht.dvd_mul).mp h2 with ha | hb
        · exact Or.inl ha
        · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
