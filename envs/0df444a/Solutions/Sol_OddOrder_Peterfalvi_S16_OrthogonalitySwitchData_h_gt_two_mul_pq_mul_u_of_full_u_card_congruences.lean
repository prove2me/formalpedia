-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.OrthogonalitySwitchData.h_gt_two_mul_pq_mul_u_of_full_u_card_congruences
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:36:01.376498+00:00
-- url     : https://prove2.me/submissions/50da3615-edf0-4147-9f50-27ccfb1216f3

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing
import Theorems.Thm_OddOrder_Peterfalvi_S16_Hypothesis_quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem cyclotomic_quotient_modEq_one_mod_base {p q : ℕ}
    (hp2 : 2 ≤ p) (hqpos : 0 < q) :
    (p ^ q - 1) / (p - 1) ≡ 1 [MOD p] := by
  have hsum_eq : ∑ k ∈ Finset.range q, p ^ k = (p ^ q - 1) / (p - 1) :=
    Nat.geomSum_eq hp2 q
  rw [← hsum_eq]
  rw [show q = (q - 1) + 1 by omega]
  rw [Finset.sum_range_succ']
  have hzero : (∑ k ∈ Finset.range (q - 1), p ^ (k + 1)) ≡ 0 [MOD p] := by
    rw [Nat.modEq_zero_iff_dvd]
    refine Finset.dvd_sum fun k _hk => ?_
    exact dvd_pow_self p (Nat.succ_ne_zero k)
  simpa using hzero.add_right 1

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/BetaVanishing.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace NonConjugateHypothesis

/-- **Peterfalvi (14.13)**: since `h = |H|` and `H` is a subgroup of the
minimal odd-order group, `h` is odd. -/
theorem h_odd [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} (nc : NonConjugateHypothesis hyp) :
    Odd nc.h := by
  rw [nc.h_eq_card_H]
  exact _hG.odd.of_dvd_nat (Subgroup.card_subgroup_dvd_card nc.Ldata.H)

end NonConjugateHypothesis

namespace OrthogonalitySwitchData

/-- **Peterfalvi (14.16)**: cardinal/congruence lower bound for the proper
`H > U` alternative.  From `h = u x`, the full cyclotomic value for `u`, and
the fixed-point-free congruences, the quotient satisfies `x ≡ 1 mod p q`; if
`x ≠ 1`, oddness forces `x > 2 p q`, hence `h > 2 p q u`. -/
theorem _root_.solution
    [Finite G] (_hG : OddOrder.BG.IsMinimalSimpleOdd G)
    {hyp : Hypothesis (G := G)} {nc : NonConjugateHypothesis hyp}
    (hu_full : hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1))
    (hu_dvd_h : hyp.base.u ∣ nc.h)
    (hh_mod_p : nc.h ≡ 1 [MOD hyp.base.p])
    (hh_mod_q : nc.h ≡ 1 [MOD hyp.base.q])
    (hu_mod_q : hyp.base.u ≡ 1 [MOD hyp.base.q])
    (hx_ne_one_of_quotient : ∀ x : ℕ, nc.h = hyp.base.u * x → x ≠ 1) :
    2 * (hyp.base.p * hyp.base.q) * hyp.base.u < nc.h := by
  rcases hu_dvd_h with ⟨x, hh_eq⟩
  have hu_mod_p : hyp.base.u ≡ 1 [MOD hyp.base.p] := by
    rw [hu_full]
    exact cyclotomic_quotient_modEq_one_mod_base
      hyp.base.p_prime.two_le hyp.base.q_prime.pos
  have hx_mod_p : x ≡ 1 [MOD hyp.base.p] := by
    have hux_mod_p : hyp.base.u * x ≡ x [MOD hyp.base.p] := by
      simpa [one_mul] using hu_mod_p.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.p] := by
      rw [hh_eq]
      exact hux_mod_p
    exact hh_mod_x.symm.trans hh_mod_p
  have hx_mod_q : x ≡ 1 [MOD hyp.base.q] := by
    have hux_mod_q : hyp.base.u * x ≡ x [MOD hyp.base.q] := by
      simpa [one_mul] using hu_mod_q.mul_right x
    have hh_mod_x : nc.h ≡ x [MOD hyp.base.q] := by
      rw [hh_eq]
      exact hux_mod_q
    exact hh_mod_x.symm.trans hh_mod_q
  have hh_odd : Odd nc.h := nc.h_odd _hG
  have hux_odd : Odd (hyp.base.u * x) := by
    rw [← hh_eq]
    exact hh_odd
  have hx_odd : Odd x := (Nat.odd_mul.mp hux_odd).2
  have hx_gt : 2 * (hyp.base.p * hyp.base.q) < x :=
    hyp.quotient_gt_two_mul_pq_of_modEq_one_mod_p_and_q
      hx_mod_p hx_mod_q hx_odd (hx_ne_one_of_quotient x hh_eq)
  have hu_pos : 0 < hyp.base.u := Odd.pos (Nat.odd_mul.mp hux_odd).1
  have hmul :
      hyp.base.u * (2 * (hyp.base.p * hyp.base.q)) < hyp.base.u * x :=
    Nat.mul_lt_mul_of_pos_left hx_gt hu_pos
  rw [hh_eq]
  nlinarith

end OrthogonalitySwitchData

end OddOrder.Peterfalvi.S16
