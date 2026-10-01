-- Prove2me | solution 1 for WeakGoldbach.verified_range_pointwise_sieve_coverage
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T13:54:38.718195+00:00
-- url     : https://prove2.me/submissions/9d94c526-0fe8-4d24-aee1-4bb35d1d9d81
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_verified_range_explicit_sieve_certificate
import Definitions.Def_GoldbachSieve
import Mathlib.Algebra.Ring.Parity

set_option autoImplicit false

theorem solution (n : Nat)
    (hlo : Nat.le (4 * 10 ^ 14) n) (hhi : Nat.le n (4 * 10 ^ 18)) (heven : Even n) :
    Exists fun p : Nat => Exists fun q : Nat =>
      And (Nat.Prime p) (And (Nat.le p 9781)
        (And (Membership.mem (GoldbachSieve.survivors (n - 9781) n 2000000000) q) (p + q = n))) := by
  have hcert := WeakGoldbach.verified_range_explicit_sieve_certificate n hlo hhi heven
  let p := Classical.choose hcert
  have htail := Classical.choose_spec hcert
  let q := Classical.choose htail
  have hparts := Classical.choose_spec htail
  have hp : Nat.Prime p := hparts.1
  have hpbound : Nat.le p 9781 := hparts.2.1
  have hqrange : q ∈ Finset.Icc (max 2 (n - 9781)) n := hparts.2.2.1
  have hsum : p + q = n := hparts.2.2.2.1
  have hclean :
      (((Finset.Icc 2 2000000000).filter Nat.Prime).filter
        (fun r => And (Dvd.dvd r q) (Not (r = q)))) = (Finset.empty : Finset Nat) :=
    hparts.2.2.2.2
  have hqsurv : q ∈ GoldbachSieve.survivors (n - 9781) n 2000000000 := by
    change q ∈ (Finset.Icc (max 2 (n - 9781)) n).filter
      (fun q => ((((Finset.Icc 2 2000000000).filter Nat.Prime).filter
        (fun r => And (Dvd.dvd r q) (Not (r = q)))).card = 0))
    apply Finset.mem_filter.mpr
    exact And.intro hqrange (by rw [hclean]; rfl)
  exact Exists.intro p (Exists.intro q
    (And.intro hp (And.intro hpbound (And.intro hqsurv hsum))))
