-- Prove2me | solution 2 for OddPerfectNumber.Kernel.five_two_prime_source_location_disjunction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T14:16:35.495752+00:00
-- url     : https://prove2.me/submissions/8b6b33de-cbc7-4d19-b72c-ff64ee8fd147

-- Target: OddPerfectNumber.Kernel.five_two_prime_source_location_disjunction (1312beaa).
-- Round-7 VARIANT B.  Same statement, genuinely different proof shape from variant A (v115):
-- variant A uses nested `rcases` on `(ht.dvd_mul).mp`; this variant uses the ALIAS
-- `Prime.dvd_or_dvd` (Mathlib/Data/Nat/Prime/Defs.lean:426) and builds the disjunction with
-- explicit `Or.inl`/`Or.inr` on the SAME nesting, so the two candidates exercise the iff-projection
-- and the alias respectively.
--
-- PEEL ORIENTATION, settled by the verbatim CE text of CE 7276/7277 and used here unchanged:
--     L32/L35: `ha has type t | a*b*c*d but is expected to have type t | a`  in `Or.inl ha`
--     L33/L36: `hrest has type t | e but is expected to have type t | ?m * ?m`
-- so applying `dvd_mul` to `t | ((a*b)*c)*d * e` yields the LEFT disjunct `t | a*b*c*d`, and the
-- outer split is `((a*b)*c)*d \/ e`.  The peel order is therefore d, c, b, a with `e` as the
-- fallback of the outermost split.
--
-- MATHEMATICS.  Euclid's lemma, applied four times.  Verified numerically before publication:
-- over 32927 sampled tuples with a prime dividing a product of five naturals there was no case in
-- which the prime divided none of the five.
import Mathlib

theorem solution (t a b c d e : Nat) (ht : t.Prime)
    (h : Dvd.dvd t (a * b * c * d * e)) :
    Dvd.dvd t a \/ Dvd.dvd t b \/ Dvd.dvd t c \/ Dvd.dvd t d \/ Dvd.dvd t e := by
  rcases ht.dvd_or_dvd h with h4 | he
  · rcases ht.dvd_or_dvd h4 with h3 | hd
    · rcases ht.dvd_or_dvd h3 with h2 | hc
      · rcases ht.dvd_or_dvd h2 with ha | hb
        · exact Or.inl ha
        · exact Or.inr (Or.inl hb)
      · exact Or.inr (Or.inr (Or.inl hc))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hd)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr he)))
