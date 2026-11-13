-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.Hypothesis.quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:27:45.891545+00:00
-- url     : https://prove2.me/submissions/d634e308-71e6-4ed1-8d15-775049c55d03

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_CoreLemmas.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas

-- ===== OddOrder/Peterfalvi/S16_CoreLemmas.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace Hypothesis

/-- Under **Peterfalvi (14.1)**, the two prime parameters are distinct. -/
theorem p_ne_q (hyp : Hypothesis (G := G)) : hyp.base.p ≠ hyp.base.q := by
  exact ne_of_gt hyp.q_lt_p

/-- **Peterfalvi (14.16)**: the parity estimate for the quotient `x = h / u`.
If `x ≡ 1` modulo both `p` and `q`, then CRT gives `x ≡ 1 mod p q`;
oddness and `x ≠ 1` force the first nontrivial possibility to be beyond
`2 p q`. -/
theorem _root_.solution
    (hyp : Hypothesis (G := G)) {x : ℕ}
    (hx_mod_p : x ≡ 1 [MOD hyp.base.p])
    (hx_mod_q : x ≡ 1 [MOD hyp.base.q])
    (hx_odd : Odd x) (hx_ne_one : x ≠ 1) :
    2 * (hyp.base.p * hyp.base.q) < x := by
  have hpq_coprime : Nat.Coprime hyp.base.p hyp.base.q :=
    (Nat.coprime_primes hyp.base.p_prime hyp.base.q_prime).mpr hyp.p_ne_q
  have hx_mod_pq : x ≡ 1 [MOD hyp.base.p * hyp.base.q] :=
    (Nat.modEq_and_modEq_iff_modEq_mul hpq_coprime).mp ⟨hx_mod_p, hx_mod_q⟩
  have hx_ge_one : 1 ≤ x := by
    rcases hx_odd with ⟨k, hk⟩
    omega
  rcases (Nat.modEq_iff_exists_eq_add hx_ge_one).mp hx_mod_pq.symm with ⟨n, hx_eq⟩
  have hn_ne_zero : n ≠ 0 := by
    intro hn0
    rw [hn0, mul_zero, add_zero] at hx_eq
    exact hx_ne_one hx_eq
  have hpq_odd : Odd (hyp.base.p * hyp.base.q) :=
    hyp.base.p_odd.mul hyp.base.q_odd
  have hn_even : Even n := by
    by_contra hn_not_even
    have hn_odd : Odd n := Nat.not_even_iff_odd.mp hn_not_even
    have hpqn_odd : Odd ((hyp.base.p * hyp.base.q) * n) :=
      hpq_odd.mul hn_odd
    have hx_even : Even x := by
      rw [hx_eq]
      exact (by norm_num : Odd 1).add_odd hpqn_odd
    exact (Nat.not_even_iff_odd.mpr hx_odd) hx_even
  have hn_ge_two : 2 ≤ n := by
    rcases hn_even with ⟨k, hk⟩
    have hk_pos : 0 < k := by
      by_contra hk_not_pos
      have hk0 : k = 0 := by omega
      subst k
      omega
    omega
  rw [hx_eq]
  nlinarith [Nat.mul_le_mul_left (hyp.base.p * hyp.base.q) hn_ge_two]

end Hypothesis

end OddOrder.Peterfalvi.S16
