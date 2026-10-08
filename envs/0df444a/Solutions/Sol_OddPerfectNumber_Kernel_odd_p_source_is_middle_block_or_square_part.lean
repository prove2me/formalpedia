-- Prove2me | solution 1 for OddPerfectNumber.Kernel.odd_p_source_is_middle_block_or_square_part
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-05T02:18:17.622703+00:00
-- url     : https://prove2.me/submissions/7505a5ec-7aa5-458c-84ed-6b33a7c57d41

-- Target: OddPerfectNumber.Kernel.odd_p_source_is_middle_block_or_square_part
--
-- MATHEMATICS.  Pure prime-support splitting, no valuation theory.
-- With `m = 3 * u * a * b * d1 * q * r` and `t.Prime`, `t | m`, Euclid's lemma
-- peels the product one factor at a time:
--
--     t | 3  \/  t | (u*a*b*d1)  \/  t | q  \/  t | r.
--
-- The hypotheses `ht3 : t != 3` and `htr : t != r` remove the first and last
-- branch: a prime dividing `3` is `3`, and a prime dividing `r` (a prime) is `r`.
-- What remains is `t = q` or `t | u*a*b*d1`.
--
-- The exclusion of `3` and of `r` as incoming sigma SOURCES is NOT proved here.
-- It is supplied by the parent from three_is_quadratic_nonresidue_mod_euler_prime
-- (f113d40e) and odd_order_source_not_minus_block_prime (240feedb), both Proved.
-- This child isolates only the arithmetic splitting.
--
-- API, verified in the pinned revision 0df444a3:
--   `Nat.Prime.dvd_mul ht : t | a * b <-> t | a \/ t | b`
--   used as `rcases (Nat.Prime.dvd_mul ht).mp h with h1 | h2` at
--   Mathlib/NumberTheory/PythagoreanTriples.lean:328.
--   `Nat.Prime.eq_one_or_self_of_dvd` and `Nat.Prime.ne_one`, read at
--   Mathlib/Data/Nat/Prime/Defs.lean:88 and :85 respectively, convert a
--   divisibility `t | 3` or `t | r` into `t = 3` or `t = r`.
import Mathlib

theorem solution {p m u a b d1 q r t : Nat}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (ht : t.Prime) (htd : Dvd.dvd t m)
    (hshape : m = 3 * u * a * b * d1 * q * r)
    (ht3 : t != 3) (htr : t != r) :
    t = q \/ Dvd.dvd t (u * a * b * d1) := by
  rw [hshape] at htd
  -- STEP 1: `t` does not divide `3`.  A prime dividing `3` is `1` or `3`; `t` is prime so
  -- `t != 1`, and `ht3` excludes `t = 3`.  Hence `t ∤ 3`.  (Note `Nat.dvd_prime` and
  -- `Prime.eq_one_or_self_of_dvd` are BOTH inapplicable: each needs the DIVISOR to divide
  -- the PRIME, i.e. `3 | t`, while we have `t | 3`.  `t = 3` is therefore excluded
  -- directly, not via a divisibility converse.)
  -- `Nat.dvd_prime Nat.prime_three : m | 3 <-> m = 1 \/ m = 3`, verified at
  -- Data/Nat/Prime/Defs.lean:181 with `prime_three` at :173.  Note the DIRECTION: this
  -- lemma takes `m | p` with `p` prime, so it is applied to `t | 3` (p := 3), NOT to
  -- `3 | t`.  Earlier generations had it exactly backwards.
  -- `ht3 : t != 3` is the BOOLEAN binder of the target, i.e. `(t != 3) = true`.  It is
  -- converted once, here, to the Prop `t != 3` (unicode `!=`), and that Prop is what the
  -- rest of the proof uses.  Note `(by simpa using ht3) h3` does NOT parse: `simpa` needs
  -- a goal and the result is not a function to apply.
  have ht3u : ¬ (t = 3) := by simpa using ht3
  have ht3' : ¬ (Dvd.dvd t 3) := by
    intro hd
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact ht.ne_one (by simpa using h1)
    · exact ht3u h3
  -- STEP 2: re-associate so the square part and the index part are single factors, then
  -- split `t | 3 * (X * Y)` as `t | 3` or `t | X * Y`.  `ht3'` closes the first branch,
  -- and the re-association forces the intended split (Lean may otherwise peel the
  -- RIGHTMOST factor of a left-associated product).
  have htru : ¬ (t = r) := by simpa using htr
  have hsplit : Dvd.dvd t (3 * ((u * a * b * d1) * (q * r))) := by
    convert htd using 1 <;> ring
  rcases (Nat.Prime.dvd_mul ht).mp hsplit with h3 | hinner
  · exact absurd h3 ht3'
  -- STEP 3: split the inner product into the square part and `q * r`.
  have hinner' : Dvd.dvd t ((u * a * b * d1) * (q * r)) := hinner
  rcases (Nat.Prime.dvd_mul ht).mp hinner' with hsq | hqr
  · exact Or.inr hsq
  rcases (Nat.Prime.dvd_mul ht).mp hqr with hdq | hdr
  · exact Or.inl ((Nat.dvd_prime hq).mp hdq |>.resolve_left ht.ne_one)
  · exact absurd ((Nat.dvd_prime hr).mp hdr |>.resolve_left ht.ne_one) htru
