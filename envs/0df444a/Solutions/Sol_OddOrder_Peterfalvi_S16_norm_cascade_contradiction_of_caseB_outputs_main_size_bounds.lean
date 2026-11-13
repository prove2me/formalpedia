-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.norm_cascade_contradiction_of_caseB_outputs_main_size_bounds
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:27:43.921786+00:00
-- url     : https://prove2.me/submissions/8f91b349-33a2-48a7-91de-b216857df3c0

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_CoreLemmas.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequalityArithmetic.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_SubgroupMCore
import Theorems.Thm_OddOrder_Peterfalvi_S16_CaseBForSData_two_q_lt_u

-- ===== OddOrder/Peterfalvi/S16_CoreLemmas.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

namespace Hypothesis

/-- Under **Peterfalvi (14.1)**, the larger prime parameter is at least `5`. -/
theorem five_le_p (hyp : Hypothesis (G := G)) : 5 ≤ hyp.base.p := by
  have hp_gt_three : 3 < hyp.base.p := lt_of_le_of_lt hyp.base.three_le_q hyp.q_lt_p
  have hp_ne_four : hyp.base.p ≠ 4 := by
    intro hp4
    have hodd : Odd 4 := by simpa [hp4] using hyp.base.p_odd
    rcases hodd with ⟨k, hk⟩
    omega
  omega

end Hypothesis

end OddOrder.Peterfalvi.S16

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

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequality.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

private theorem mul_pred_lt_three_pow_pred {p : ℕ} (hp : 5 ≤ p) :
    p * (p - 1) < 3 ^ (p - 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hstep : (p + 1) * p < 3 * (p * (p - 1)) := by
        have hfactor : p + 1 < 3 * (p - 1) := by omega
        have hmul := Nat.mul_lt_mul_of_pos_right hfactor (by omega : 0 < p)
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
      calc
        (p + 1) * ((p + 1) - 1) = (p + 1) * p := by rw [Nat.add_sub_cancel_right]
        _ < 3 * (p * (p - 1)) := hstep
        _ < 3 * 3 ^ (p - 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 3 ^ p := by
          calc
            3 * 3 ^ (p - 1) = 3 ^ (p - 1) * 3 := by rw [mul_comm]
            _ = 3 ^ ((p - 1) + 1) := by rw [pow_succ]
            _ = 3 ^ p := by rw [show (p - 1) + 1 = p by omega]

private theorem p_mul_q_lt_q_pow_pred_of_five_le {p q : ℕ}
    (hp5 : 5 ≤ p) (hq3 : 3 ≤ q) (hqp : q < p) :
    p * q < q ^ (p - 1) := by
  have hq_le_pred : q ≤ p - 1 := by omega
  have hpq_le : p * q ≤ p * (p - 1) := Nat.mul_le_mul_left p hq_le_pred
  have hpq_lt_three : p * q < 3 ^ (p - 1) :=
    lt_of_le_of_lt hpq_le (mul_pred_lt_three_pow_pred hp5)
  have hthree_le_qpow : 3 ^ (p - 1) ≤ q ^ (p - 1) :=
    Nat.pow_le_pow_left hq3 (p - 1)
  exact lt_of_lt_of_le hpq_lt_three hthree_le_qpow

namespace CaseBForTData

/-- The T-side case-(9.7.b) cyclotomic value in **Peterfalvi (14.4)** is already
larger than `p q`.  This is the cyclotomic lower consequence consumed by the
norm-cascade contradiction in (14.11.4). -/
theorem pq_lt_v {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    hyp.base.p * hyp.base.q < hyp.base.v := by
  have hpow : hyp.base.p * hyp.base.q < hyp.base.q ^ (hyp.base.p - 1) :=
    p_mul_q_lt_q_pow_pred_of_five_le hyp.five_le_p hyp.base.three_le_q hyp.q_lt_p
  have hleQ := cyclotomic_quotient_sub_one_ge_pow_pred
    (q := hyp.base.q) (p := hyp.base.p) hyp.base.q_prime.two_le hyp.base.p_prime.two_le
  have hle : hyp.base.q ^ (hyp.base.p - 1) ≤
      (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1) - 1 := by
    exact_mod_cast hleQ
  rw [data.v_eq]
  exact lt_of_lt_of_le (lt_of_lt_of_le hpow hle)
    (Nat.sub_le ((hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1)) 1)

/-- The T-side case-(9.7.b) lower bound also gives the size hypothesis
`v > 2 p` needed in the (14.11.4) norm cascade. -/
theorem two_p_lt_v {hyp : Hypothesis (G := G)} (data : CaseBForTData hyp) :
    2 * hyp.base.p < hyp.base.v := by
  have hq_gt_two : 2 < hyp.base.q := by
    have hq3 : 3 ≤ hyp.base.q := hyp.base.three_le_q
    omega
  have hp_pos : 0 < hyp.base.p := hyp.base.p_prime.pos
  have hmul : hyp.base.p * 2 < hyp.base.p * hyp.base.q :=
    Nat.mul_lt_mul_of_pos_left hq_gt_two hp_pos
  have h2p_lt_pq : 2 * hyp.base.p < hyp.base.p * hyp.base.q := by
    simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
  exact lt_trans h2p_lt_pq data.pq_lt_v

end CaseBForTData

end OddOrder.Peterfalvi.S16

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/SubgroupMCore.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- Pure arithmetic estimate used in **Peterfalvi (14.11.4)**.  Once the
norm calculation reduces the error terms to `2 / (p q) + 1 / (u q) + 1 / (v p)`,
the Section 16 size assumptions `u > 2q`, `v > 2p`, and `q < p` bound that error
strictly by `1 / q`. -/
theorem norm_error_terms_lt_inv_q {p q u v : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v) :
    (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
        1 / ((v * p : ℕ) : ℚ) < 1 / (q : ℚ) := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hupos_nat : 0 < u := by omega
  have hvpos_nat : 0 < v := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hupos : (0 : ℚ) < u := by exact_mod_cast hupos_nat
  have hvpos : (0 : ℚ) < v := by exact_mod_cast hvpos_nat
  have hq3q : (3 : ℚ) ≤ q := by exact_mod_cast hq3
  have hqpq : (q : ℚ) < p := by exact_mod_cast hqp
  have huq : (2 : ℚ) * q < u := by exact_mod_cast hu
  have hvp : (2 : ℚ) * p < v := by exact_mod_cast hv
  have hterm1 : (2 : ℚ) / ((p * q : ℕ) : ℚ) < 2 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    exact div_lt_div_of_pos_left (by norm_num) (mul_pos hqpos hqpos)
      (mul_lt_mul_of_pos_right hqpq hqpos)
  have hterm2 : (1 : ℚ) / ((u * q : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hden : (2 : ℚ) * q * q < u * q := by nlinarith [huq, hqpos]
    have hcore : (1 : ℚ) / (u * q) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hterm3 : (1 : ℚ) / ((v * p : ℕ) : ℚ) < 1 / ((2 * q * q : ℕ) : ℚ) := by
    have hsq : (q : ℚ) * q < p * p := by nlinarith [hqpq, hqpos, hppos]
    have hden : (2 : ℚ) * q * q < v * p := by nlinarith [hsq, hvp, hppos]
    have hcore : (1 : ℚ) / (v * p) < 1 / (2 * q * q) :=
      one_div_lt_one_div_of_lt (by positivity : (0 : ℚ) < 2 * q * q) hden
    simpa [Nat.cast_mul, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hsum :
      (2 : ℚ) / ((p * q : ℕ) : ℚ) + 1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ) <
        2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) := by
    nlinarith [hterm1, hterm2, hterm3]
  have hsum_eq :
      2 / ((q * q : ℕ) : ℚ) + 1 / ((2 * q * q : ℕ) : ℚ) +
          1 / ((2 * q * q : ℕ) : ℚ) = 3 / ((q * q : ℕ) : ℚ) := by
    norm_num [Nat.cast_mul]
    field_simp [hqpos.ne']
    ring
  have hthree_le : (3 : ℚ) / ((q * q : ℕ) : ℚ) ≤ 1 / (q : ℚ) := by
    norm_num [Nat.cast_mul]
    have hmul_nonneg : 0 ≤ (q : ℚ) * ((q : ℚ) - 3) :=
      mul_nonneg (le_of_lt hqpos) (sub_nonneg.mpr hq3q)
    field_simp [hqpos.ne']
    nlinarith [hmul_nonneg]
  nlinarith [hsum, hsum_eq, hthree_le]

/-- Arithmetic endpoint for **Peterfalvi (14.11.4)**.  If the norm calculation
has already yielded the displayed bound from the text, then the lower bound
`k > 2 p v` and the cyclotomic lower consequence `p q < v` are contradictory. -/
theorem norm_cascade_contradiction {p q u v k : ℕ}
    (hq3 : 3 ≤ q) (hqp : q < p) (hu : 2 * q < u) (hv : 2 * p < v)
    (hk : 2 * p * v < k) (hvlarge : p * q < v)
    (hbound :
      (1 : ℚ) / (p : ℚ) + 1 / (q : ℚ) ≤
        ((p * q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((p * q : ℕ) : ℚ) +
          1 / ((u * q : ℕ) : ℚ) +
          1 / ((v * p : ℕ) : ℚ)) :
    False := by
  have hqpos_nat : 0 < q := by omega
  have hppos_nat : 0 < p := by omega
  have hvpos_nat : 0 < v := by omega
  have hkpos_nat : 0 < k := by omega
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hkpos : (0 : ℚ) < k := by exact_mod_cast hkpos_nat
  have hsmall := norm_error_terms_lt_inv_q (p := p) (q := q) (u := u) (v := v)
    hq3 hqp hu hv
  have hpinv_lt : (1 : ℚ) / (p : ℚ) < ((p * q : ℕ) : ℚ) / (k : ℚ) := by
    nlinarith [hbound, hsmall]
  have hk_lt : (k : ℚ) < (p : ℚ) * (p : ℚ) * (q : ℚ) := by
    field_simp [Nat.cast_mul, hppos.ne', hqpos.ne', hkpos.ne'] at hpinv_lt
    norm_num [Nat.cast_mul] at hpinv_lt
    nlinarith [hpinv_lt]
  have hk_gt : ((2 * p * v : ℕ) : ℚ) < k := by exact_mod_cast hk
  have hvlargeq : ((p * q : ℕ) : ℚ) < v := by exact_mod_cast hvlarge
  norm_num [Nat.cast_mul] at hk_gt hvlargeq
  nlinarith [hk_lt, hk_gt, hvlargeq, hppos]

/-- **Peterfalvi (14.11.4)** arithmetic consumer with the T-side case-(9.7.b)
data already materialized.  The T-side data supplies both `p q < v` and
`2 p < v`, so the remaining inputs are exactly the S-side lower bound on `u`,
the `k > 2 p v` lower bound, and the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_T_caseB {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (hu : 2 * hyp.base.q < hyp.base.u) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction hyp.base.three_le_q hyp.q_lt_p hu
    Tdata.two_p_lt_v hk Tdata.pq_lt_v hbound

/-- **Peterfalvi (14.11.4)** arithmetic consumer with both case-(9.7.b) data
packages materialized.  The S-side data supplies `2 q < u`; the T-side data
supplies `2 p < v` and `p q < v`. -/
theorem norm_cascade_contradiction_of_caseB_data {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) {k : ℕ}
    (hk : 2 * hyp.base.p * hyp.base.v < k)
    (hbound :
      (1 : ℚ) / (hyp.base.p : ℚ) + 1 / (hyp.base.q : ℚ) ≤
        ((hyp.base.p * hyp.base.q : ℕ) : ℚ) / (k : ℚ) +
          2 / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.u * hyp.base.q : ℕ) : ℚ) +
          1 / ((hyp.base.v * hyp.base.p : ℕ) : ℚ)) :
    False := by
  exact norm_cascade_contradiction_of_T_caseB Tdata Sdata.two_q_lt_u hk hbound

/-- **Peterfalvi (14.11.4)** consumer after the first numerical output of
`main_size_bounds` has supplied `k > 2 p v`.  The remaining non-arithmetic work
is precisely to produce the displayed norm inequality. -/
theorem norm_cascade_contradiction_of_main_size_bound {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v)
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_caseB_data Tdata Sdata hsize hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact three-part numerical output
of **Peterfalvi (14.11.1)**.  Only the first component, `k > 2 p v`, is needed
by the norm-cascade contradiction; the remaining components stay available to
match the theorem output without weakening its shape. -/
theorem norm_cascade_contradiction_of_caseB_data_main_size_bounds
    {hyp : Hypothesis (G := G)}
    (Tdata : CaseBForTData hyp) (Sdata : CaseBForSData hyp) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  exact norm_cascade_contradiction_of_main_size_bound Tdata Sdata Mdata hsize.1 hbound

/-- **Peterfalvi (14.11.4)** consumer for the exact output shapes of
`caseB_for_T`, `caseB_for_S`, and `main_size_bounds`. -/
theorem _root_.solution
    {hyp : Hypothesis (G := G)}
    (hT : ∃ data : CaseBForTData hyp,
      data.caseB_formula ∧ hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hS : ∃ data : CaseBForSData hyp, data.caseB_formula) (Mdata : MHypothesis hyp)
    (hsize : Mdata.k > 2 * hyp.base.p * hyp.base.v ∧
      (((Mdata.k - 1 : ℕ) : ℚ) / (Mdata.e : ℚ) >
        ((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ)) ∧
      (((hyp.base.v - 1 : ℕ) : ℚ) / (hyp.base.p : ℚ) >
        ((hyp.base.u - 1 : ℕ) : ℚ) / (hyp.base.q : ℚ)))
    (hbound : normCascadeBound hyp Mdata.k) :
    False := by
  rcases hT with ⟨Tdata, _hTcase, _hv⟩
  rcases hS with ⟨Sdata, _hScase⟩
  exact norm_cascade_contradiction_of_caseB_data_main_size_bounds Tdata Sdata Mdata
    hsize hbound

end OddOrder.Peterfalvi.S16
