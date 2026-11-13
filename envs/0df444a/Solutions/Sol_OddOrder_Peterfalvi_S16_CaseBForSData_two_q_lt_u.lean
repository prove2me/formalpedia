-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.CaseBForSData.two_q_lt_u
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:19:37.321973+00:00
-- url     : https://prove2.me/submissions/8a84f5d6-d241-4704-bfcf-0d972fb92032

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequalityArithmetic.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupL

-- ===== OddOrder/Peterfalvi/S15_SAndT_Setup/OrderDetermination.lean =====
namespace OddOrder.Peterfalvi.S15

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise IsMulCommutative

variable {G : Type*} [Group G]

/-- The `p ≡ 1 [MOD q]` divisibility part of **Peterfalvi (13.14)**. -/
theorem cyclotomic_quotient_dvd_of_modEq_one {p q : ℕ} (hp : p.Prime)
    (hpq : p ≡ 1 [MOD q]) :
    q ∣ (p ^ q - 1) / (p - 1) := by
  rw [← Nat.geomSum_eq hp.two_le q]
  rw [← Nat.modEq_zero_iff_dvd]
  have hterms : (∑ k ∈ Finset.range q, p ^ k) ≡ ∑ k ∈ Finset.range q, 1 [MOD q] :=
    Nat.ModEq.sum fun k _ => by simpa using Nat.ModEq.pow k hpq
  have hsum_one : (∑ k ∈ Finset.range q, 1 : ℕ) = q := by simp
  exact hterms.trans (by simp [hsum_one])

end OddOrder.Peterfalvi.S15

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequalityArithmetic.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

theorem cyclotomic_quotient_sub_one_ge_pow_pred {q p : ℕ}
    (hq2 : 2 ≤ q) (hp2 : 2 ≤ p) :
    ((q ^ (p - 1) : ℕ) : ℚ) ≤ (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) := by
  have hsum_eq : ∑ k ∈ Finset.range p, q ^ k = (q ^ p - 1) / (q - 1) :=
    Nat.geomSum_eq hq2 p
  have hle_rest : q ^ (p - 1) ≤ ∑ k ∈ Finset.range (p - 1), q ^ (k + 1) := by
    have hlast_mem : p - 2 ∈ Finset.range (p - 1) := by
      simp
      omega
    have hnonneg : ∀ k ∈ Finset.range (p - 1), 0 ≤ q ^ (k + 1) := by
      intro k _hk
      exact Nat.zero_le _
    have hsingle := Finset.single_le_sum hnonneg hlast_mem
    simpa [show p - 2 + 1 = p - 1 by omega] using hsingle
  have hsum_succ : ∑ k ∈ Finset.range p, q ^ k =
      (∑ k ∈ Finset.range (p - 1), q ^ (k + 1)) + 1 := by
    rw [show p = (p - 1) + 1 by omega]
    rw [Finset.sum_range_succ']
    simp
  have hle_sum : q ^ (p - 1) + 1 ≤ ∑ k ∈ Finset.range p, q ^ k := by
    rw [hsum_succ]
    omega
  have hnat : q ^ (p - 1) ≤ (q ^ p - 1) / (q - 1) - 1 := by
    rw [← hsum_eq]
    omega
  exact_mod_cast hnat

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupL.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace CaseBForSData

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
`p ≡ 1 mod q` branch gives the divided cyclotomic value of `u`. -/
theorem u_eq_of_p_modEq_one {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) :=
  data.order_u_eq_of_p_modEq_one

/-- In the S-side case-(9.7.b) conclusion of **Peterfalvi (14.6)**, the
non-`p ≡ 1 mod q` branch gives the full cyclotomic value of `u`. -/
theorem u_eq_of_not_modEq_one {hyp : Hypothesis (G := G)}
    (data : CaseBForSData hyp) :
    ¬ hyp.base.p ≡ 1 [MOD hyp.base.q] →
      hyp.base.u = (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
  data.order_u_eq_of_not_modEq_one

end CaseBForSData

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

private theorem two_mul_sq_lt_pow_pred_of_odd_lt {p q : ℕ}
    (hpodd : Odd p) (hqodd : Odd q) (hq3 : 3 ≤ q) (hqp : q < p) :
    2 * q * q < p ^ (q - 1) := by
  by_cases hq_three : q = 3
  · subst q
    have hp_gt_three : 3 < p := by simpa using hqp
    have hp5 : 5 ≤ p := by
      have hp_ne_four : p ≠ 4 := by
        intro hp4
        have hodd : Odd 4 := by simpa [hp4] using hpodd
        rcases hodd with ⟨k, hk⟩
        omega
      omega
    have hpow2 : 2 * 3 * 3 < p ^ 2 := by
      nlinarith
    simpa using hpow2
  · have hq5 : 5 ≤ q := by
      have hq_ne_four : q ≠ 4 := by
        intro hq4
        have hodd : Odd 4 := by simpa [hq4] using hqodd
        rcases hodd with ⟨k, hk⟩
        omega
      omega
    have hq_pos : 0 < q := by omega
    have hq_sq_pos : 0 < q * q := Nat.mul_pos hq_pos hq_pos
    have htwo_lt_qsq : 2 < q * q := by nlinarith
    have hlt_q4 : 2 * (q * q) < (q * q) * (q * q) :=
      Nat.mul_lt_mul_of_pos_right htwo_lt_qsq hq_sq_pos
    have hq4_le_p4 : q ^ 4 ≤ p ^ 4 :=
      Nat.pow_le_pow_left (Nat.le_of_lt hqp) 4
    have hp_pos : 0 < p := by omega
    have hp4_le : p ^ 4 ≤ p ^ (q - 1) :=
      Nat.pow_le_pow_right hp_pos (by omega : 4 ≤ q - 1)
    calc
      2 * q * q = 2 * (q * q) := by ring
      _ < (q * q) * (q * q) := hlt_q4
      _ = q ^ 4 := by ring
      _ ≤ p ^ 4 := hq4_le_p4
      _ ≤ p ^ (q - 1) := hp4_le

namespace CaseBForSData

/-- The S-side case-(9.7.b) cyclotomic value in **Peterfalvi (14.6)** is larger
than `2 q`.  This is the S-side size input consumed by the norm-cascade
contradiction in (14.11.4), including the additional division by `q` in the
`p ≡ 1 mod q` branch. -/
theorem _root_.solution {hyp : Hypothesis (G := G)} (data : CaseBForSData hyp) :
    2 * hyp.base.q < hyp.base.u := by
  have hpow_sq :
      2 * hyp.base.q * hyp.base.q < hyp.base.p ^ (hyp.base.q - 1) :=
    two_mul_sq_lt_pow_pred_of_odd_lt hyp.base.p_odd hyp.base.q_odd
      hyp.base.three_le_q hyp.q_lt_p
  have hq_gt_one : 1 < hyp.base.q := hyp.base.q_prime.one_lt
  have htwoq_pos : 0 < 2 * hyp.base.q :=
    Nat.mul_pos (by norm_num) hyp.base.q_prime.pos
  have htwoq_lt_twoqq : 2 * hyp.base.q < 2 * hyp.base.q * hyp.base.q := by
    have hmul := Nat.mul_lt_mul_of_pos_left hq_gt_one htwoq_pos
    simpa [mul_assoc] using hmul
  have hpow : 2 * hyp.base.q < hyp.base.p ^ (hyp.base.q - 1) :=
    lt_trans htwoq_lt_twoqq hpow_sq
  have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
    (q := hyp.base.p) (p := hyp.base.q) hyp.base.p_prime.two_le hyp.base.q_prime.two_le
  have hle : hyp.base.p ^ (hyp.base.q - 1) ≤
      (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) - 1 := by
    exact_mod_cast hleQ
  have hfull_gt_twoq :
      2 * hyp.base.q < (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le hpow hle)
      (Nat.sub_le ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) 1)
  have hfull_gt_twoqq :
      2 * hyp.base.q * hyp.base.q <
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
    lt_of_lt_of_le (lt_of_lt_of_le hpow_sq hle)
      (Nat.sub_le ((hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1)) 1)
  by_cases hmod : hyp.base.p ≡ 1 [MOD hyp.base.q]
  · rw [data.u_eq_of_p_modEq_one hmod]
    have hdvd : hyp.base.q ∣ (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) :=
      OddOrder.Peterfalvi.S15.cyclotomic_quotient_dvd_of_modEq_one
        hyp.base.p_prime hmod
    have hlt_div :
        2 * hyp.base.q <
          (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q := by
      rw [Nat.lt_div_iff_mul_lt' hdvd]
      simpa [mul_assoc, mul_comm, mul_left_comm] using hfull_gt_twoqq
    rw [show (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.q * (hyp.base.p - 1)) =
        (hyp.base.p ^ hyp.base.q - 1) / (hyp.base.p - 1) / hyp.base.q by
      rw [Nat.div_div_eq_div_mul]
      rw [Nat.mul_comm]]
    exact hlt_div
  · rw [data.u_eq_of_not_modEq_one hmod]
    exact hfull_gt_twoq

end CaseBForSData

end OddOrder.Peterfalvi.S16
