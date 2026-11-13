-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.Hypothesis.caseB_forces_q_three_and_p_five
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T17:37:30.766052+00:00
-- url     : https://prove2.me/submissions/602aca86-5231-40b8-8d83-68d16a8476f8

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequalityArithmetic.lean
--   OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLM.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_Peterfalvi_S16_NonExistenceG_BetaVanishing

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequalityArithmetic.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- A small explicit upper bound for e, used in Peterfalvi (14.8.a). -/
private theorem real_exp_one_le_three : Real.exp 1 ≤ 3 := by
  have h :=
    Complex.exp_bound_sq (0 : ℂ) ((1 : ℝ) : ℂ) (by norm_num : ‖((1 : ℝ) : ℂ)‖ ≤ 1)
  rw [Complex.exp_zero] at h
  norm_num at h
  change ‖Complex.exp (((1 : ℝ) : ℂ)) - 1 - 1‖ ≤ (1 : ℝ) at h
  have hsq : ‖Complex.exp (((1 : ℝ) : ℂ)) - 1 - 1‖ ^ 2 ≤ (1 : ℝ) ^ 2 := by
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply] at hsq
  simp [Complex.exp_re, Complex.exp_im] at hsq
  have hupper : Real.exp 1 - 2 ≤ 1 := by nlinarith
  linarith

/-- Taylor's quadratic upper bound for exp on [0,1], in the form used by (14.8.a). -/
private theorem real_exp_le_quadratic {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x ^ 2 := by
  have hxnorm : ‖((x : ℝ) : ℂ)‖ ≤ 1 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0] using h1
  have h := Complex.exp_bound_sq (0 : ℂ) ((x : ℝ) : ℂ) hxnorm
  rw [Complex.exp_zero] at h
  have hnorm : ‖Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ)‖ ≤ x ^ 2 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg h0, pow_two] using h
  have hre := Complex.re_le_norm (Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ))
  have hre_eq :
      (Complex.exp (((x : ℝ) : ℂ)) - 1 - ((x : ℝ) : ℂ)).re = Real.exp x - 1 - x := by
    simp [Complex.exp_re]
  have hdiff : Real.exp x - 1 - x ≤ x ^ 2 := by
    rw [← hre_eq]
    exact hre.trans hnorm
  linarith

private theorem one_add_inv_le_log_of_five_le {q : ℕ} (hq : 5 ≤ q) :
    1 + (1 / (q : ℝ)) ≤ Real.log q := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  rw [Real.le_log_iff_exp_le hqpos]
  have hqge : (5 : ℝ) ≤ q := by exact_mod_cast hq
  calc
    Real.exp (1 + 1 / (q : ℝ)) = Real.exp 1 * Real.exp (1 / (q : ℝ)) := by
      rw [Real.exp_add]
    _ ≤ 3 * (1 + 1 / (q : ℝ) + (1 / (q : ℝ)) ^ 2) := by
      have hsmall : Real.exp (1 / (q : ℝ)) ≤
          1 + 1 / (q : ℝ) + (1 / (q : ℝ)) ^ 2 :=
        real_exp_le_quadratic (by positivity) (by
          field_simp [hqpos.ne']
          exact_mod_cast (le_trans (by norm_num : 1 ≤ 5) hq))
      exact mul_le_mul real_exp_one_le_three hsmall (Real.exp_nonneg _) (by norm_num)
    _ ≤ q := by
      have hs : 0 ≤ (q : ℝ) ^ 2 := sq_nonneg _
      have hcube : 5 * (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by nlinarith [hqge, hs]
      have hquad : 3 * ((q : ℝ) * ((q : ℝ) + 1) + 1) ≤ 5 * (q : ℝ) ^ 2 := by
        nlinarith [hqge, hs]
      field_simp [hqpos.ne']
      nlinarith [hcube, hquad]

private theorem log_div_succ_lt_of_five_le {p q : ℕ} (hq : 5 ≤ q) (hqp : q < p) :
    Real.log (p : ℝ) / ((p : ℝ) + 1) < Real.log (q : ℝ) / ((q : ℝ) + 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  have hppos : (0 : ℝ) < p := hqpos.trans (by exact_mod_cast hqp)
  have hdenp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hdenq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  rw [div_lt_div_iff₀ hdenp hdenq]
  have hratio_pos : (0 : ℝ) < (p : ℝ) / (q : ℝ) := div_pos hppos hqpos
  have hratio_ne : (p : ℝ) / (q : ℝ) ≠ 1 := by
    intro h
    field_simp [hqpos.ne'] at h
    have hpq : p = q := by exact_mod_cast h
    omega
  have hlog_ratio := Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
  have hlog_div := Real.log_div hppos.ne' hqpos.ne'
  have hlogp_bound : Real.log (p : ℝ) < Real.log (q : ℝ) + ((p : ℝ) / (q : ℝ) - 1) := by
    nlinarith [hlog_ratio, hlog_div]
  have hmul := mul_lt_mul_of_pos_right hlogp_bound hdenq
  have hlogq_lower : ((q : ℝ) + 1) / (q : ℝ) ≤ Real.log (q : ℝ) := by
    have h := one_add_inv_le_log_of_five_le hq
    field_simp [hqpos.ne'] at h ⊢
    exact h
  have hupper :
      (Real.log (q : ℝ) + ((p : ℝ) / (q : ℝ) - 1)) * ((q : ℝ) + 1) ≤
        Real.log (q : ℝ) * ((p : ℝ) + 1) := by
    have hpq_nonneg : 0 ≤ (p : ℝ) - (q : ℝ) := by
      have hpqle : (q : ℝ) ≤ p := by exact_mod_cast (le_of_lt hqp)
      linarith
    have hlogq_lower' : (q : ℝ) + 1 ≤ Real.log (q : ℝ) * (q : ℝ) := by
      rwa [div_le_iff₀ hqpos] at hlogq_lower
    have hmul_nonneg :
        ((p : ℝ) - (q : ℝ)) * ((q : ℝ) + 1) ≤
          ((p : ℝ) - (q : ℝ)) * (Real.log (q : ℝ) * (q : ℝ)) :=
      mul_le_mul_of_nonneg_left hlogq_lower' hpq_nonneg
    field_simp [hqpos.ne']
    nlinarith [hmul_nonneg]
  exact hmul.trans_le hupper

private theorem q_pow_gt_p_pow_of_five_le {p q : ℕ} (hq : 5 ≤ q) (hqp : q < p) :
    p ^ (q + 1) < q ^ (p + 1) := by
  have hqpos : (0 : ℝ) < q := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 5) hq)
  have hppos : (0 : ℝ) < p := hqpos.trans (by exact_mod_cast hqp)
  have hdenp : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  have hdenq : (0 : ℝ) < (q : ℝ) + 1 := by positivity
  have hfrac := log_div_succ_lt_of_five_le (p := p) (q := q) hq hqp
  rw [div_lt_div_iff₀ hdenp hdenq] at hfrac
  have hlogpow : Real.log (((p : ℝ) ^ (q + 1))) < Real.log (((q : ℝ) ^ (p + 1))) := by
    rw [Real.log_pow, Real.log_pow]
    norm_num
    nlinarith [hfrac]
  have hreal : ((p : ℝ) ^ (q + 1)) < ((q : ℝ) ^ (p + 1)) :=
    (Real.log_lt_log_iff (pow_pos hppos _) (pow_pos hqpos _)).mp hlogpow
  exact_mod_cast hreal

private theorem fourth_lt_three_pow_succ {p : ℕ} (hp : 5 ≤ p) :
    p ^ 4 < 3 ^ (p + 1) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hstep : (p + 1) ^ 4 < 3 * p ^ 4 := by
        have hpz : (5 : ℤ) ≤ p := by exact_mod_cast hp
        have hz : ((p + 1 : ℤ) ^ 4 < 3 * (p : ℤ) ^ 4) := by
          nlinarith [hpz, sq_nonneg ((p : ℤ) - 5), sq_nonneg ((p : ℤ) - 4),
            sq_nonneg ((p : ℤ) - 3), sq_nonneg ((p : ℤ) - 2),
            sq_nonneg ((p : ℤ) - 1), sq_nonneg (p : ℤ)]
        exact_mod_cast hz
      calc
        (p + 1) ^ 4 < 3 * p ^ 4 := hstep
        _ < 3 * 3 ^ (p + 1) := Nat.mul_lt_mul_of_pos_left ih (by norm_num)
        _ = 3 ^ (p + 2) := by
          rw [show p + 2 = p + 1 + 1 by omega, pow_succ]
          ring

private theorem q_pow_gt_p_pow_of_q_eq_three {p q : ℕ} (hq : q = 3) (hp : 5 ≤ p) :
    p ^ (q + 1) < q ^ (p + 1) := by
  subst q
  simpa using fourth_lt_three_pow_succ hp

/-- **Peterfalvi (14.8.a)**: for odd prime parameters with q < p,
q^(p+1) strictly dominates p^(q+1). -/
theorem q_pow_gt_p_pow {p q : ℕ} (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q)
    (hqp : q < p) :
    q ^ (p + 1) > p ^ (q + 1) := by
  by_cases hq3 : q = 3
  · have hp5 : 5 ≤ p := by
      have hp4 : p ≠ 4 := by
        intro hp4
        subst p
        rcases hpodd with ⟨k, hk⟩
        omega
      omega
    exact q_pow_gt_p_pow_of_q_eq_three hq3 hp5
  · have hq_ne_two : q ≠ 2 := by
      intro hq2
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    have hq_three : 3 ≤ q := by
      have htwo : 2 ≤ q := hq.two_le
      omega
    have hq_ne_four : q ≠ 4 := by
      intro hq4
      subst q
      rcases hqodd with ⟨k, hk⟩
      omega
    have hq5 : 5 ≤ q := by omega
    exact q_pow_gt_p_pow_of_five_le hq5 hqp

namespace Hypothesis

/-- The arithmetic part of Peterfalvi (14.8) under the Section 16 bundle. -/
theorem q_pow_gt_p_pow (hyp : Hypothesis (G := G)) :
    hyp.base.q ^ (hyp.base.p + 1) > hyp.base.p ^ (hyp.base.q + 1) :=
  OddOrder.Peterfalvi.S16.q_pow_gt_p_pow hyp.base.q_prime hyp.base.p_odd hyp.base.q_odd hyp.q_lt_p

end Hypothesis

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

-- ===== OddOrder/Peterfalvi/S16_NonExistenceG/ComparingLM.lean =====
namespace OddOrder.Peterfalvi.S16

open OddOrder.GroupTheory

open OddOrder.RepresentationTheory

open OddOrder.Isaacs

open scoped Pointwise

open scoped BigOperators

variable {G : Type*} [Group G]

/-- For `p ≥ 7`, `p² ≤ 3^(p-3)`: the monotonicity input for the `p = 5` step of Peterfalvi
(14.14.b).
The paper's `f(x) = 3^(x-3)/x²` is increasing for `x ≥ 2` (`f(x+1)/f(x) = 3(1 − 1/(x+1))² > 1`);
this
is the integer form `p² ≤ 3^(p-3)` proved by induction from `p = 7` (`7² = 49 ≤ 81 = 3⁴`). -/
private theorem sq_le_three_pow_sub_three {p : ℕ} (hp : 7 ≤ p) : p ^ 2 ≤ 3 ^ (p - 3) := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ p hp ih =>
      have hsucc : 3 ^ (p + 1 - 3) = 3 * 3 ^ (p - 3) := by
        rw [show p + 1 - 3 = (p - 3) + 1 by omega, pow_succ]; ring
      rw [hsucc]
      calc (p + 1) ^ 2 ≤ 3 * p ^ 2 := by nlinarith [hp]
        _ ≤ 3 * 3 ^ (p - 3) := by gcongr

namespace Hypothesis

/-- **Peterfalvi (14.14.b)/(14.15) arithmetic core**: in case (b) of the orthogonality switch, the
`(β_L, ψ)`-pairing bound `(v−1)/(pq) ≤ pq−1` together with the (14.4) cyclotomic value
`v = (q^p−1)/(q−1)` and the (14.8.a) exponential comparison `q^(p+1) > p^(q+1)` force the
exceptional primes `q = 3` and `p = 5`.

Proof (Pf p.91): `(v−1)/(pq) < pq` gives `q^(p−1) ≤ v−1 < p²q²`, hence `q^(p−3) < p²`.  By (14.8.a)
`q^(p+1) > p^(q+1)` and `q < p`, one gets `q^(p−3) > p^(q−3)`, so `p^(q−3) < p²`, whence `q = 3`.
Then `3^(p−3) < p²`, contradicting `p² ≤ 3^(p−3)` for `p ≥ 7`, so `p = 5`. -/
theorem _root_.solution (hyp : Hypothesis (G := G))
    (hv : hyp.base.v = (hyp.base.q ^ hyp.base.p - 1) / (hyp.base.q - 1))
    (hbound : ((hyp.base.v - 1 : ℕ) : ℚ) / ((hyp.base.p * hyp.base.q : ℕ) : ℚ) ≤
      ((hyp.base.p * hyp.base.q - 1 : ℕ) : ℚ)) :
    hyp.base.q = 3 ∧ hyp.base.p = 5 := by
  have hp_prime := hyp.base.p_prime
  have hq_prime := hyp.base.q_prime
  have hqp : hyp.base.q < hyp.base.p := hyp.q_lt_p
  have hq3le : 3 ≤ hyp.base.q := by
    rcases hyp.base.q_odd with ⟨k, hk⟩; have := hq_prime.two_le; omega
  have hp5le : 5 ≤ hyp.base.p := by rcases hyp.base.p_odd with ⟨k, hk⟩; omega
  -- Step 1: `v − 1 < p² q²` from the case-(b) bound.
  have hpq_pos : 0 < hyp.base.p * hyp.base.q := Nat.mul_pos hp_prime.pos hq_prime.pos
  have hpqQ : (0 : ℚ) < ((hyp.base.p * hyp.base.q : ℕ) : ℚ) := by exact_mod_cast hpq_pos
  have hv1_le : (hyp.base.v - 1 : ℕ) ≤
      (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q) := by
    have h := (div_le_iff₀ hpqQ).mp hbound
    exact_mod_cast h
  have hv1_lt : hyp.base.v - 1 < hyp.base.p ^ 2 * hyp.base.q ^ 2 := by
    have hlt : (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q)
        < (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) :=
      mul_lt_mul_of_pos_right (by omega) hpq_pos
    calc hyp.base.v - 1
        ≤ (hyp.base.p * hyp.base.q - 1) * (hyp.base.p * hyp.base.q) := hv1_le
      _ < (hyp.base.p * hyp.base.q) * (hyp.base.p * hyp.base.q) := hlt
      _ = hyp.base.p ^ 2 * hyp.base.q ^ 2 := by ring
  -- Step 2: `q^(p−1) ≤ v − 1` from the geometric-sum lower bound.
  have hlow : hyp.base.q ^ (hyp.base.p - 1) ≤ hyp.base.v - 1 := by
    have h := cyclotomic_quotient_sub_one_ge_pow_pred hq_prime.two_le hp_prime.two_le
    rw [← hv] at h
    exact_mod_cast h
  -- Step 3: `q^(p−3) < p²`.
  have hqpm3 : hyp.base.q ^ (hyp.base.p - 3) < hyp.base.p ^ 2 := by
    have he : hyp.base.q ^ (hyp.base.p - 1)
        = hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2 := by
      rw [← pow_add]; congr 1; omega
    have hlt : hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2
        < hyp.base.p ^ 2 * hyp.base.q ^ 2 :=
      calc hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 2
          = hyp.base.q ^ (hyp.base.p - 1) := he.symm
        _ ≤ hyp.base.v - 1 := hlow
        _ < hyp.base.p ^ 2 * hyp.base.q ^ 2 := hv1_lt
    exact lt_of_mul_lt_mul_right hlt (Nat.zero_le _)
  -- Step 4: `p^(q−3) < q^(p−3)` from (14.8.a).
  have hkey : hyp.base.p ^ (hyp.base.q + 1) < hyp.base.q ^ (hyp.base.p + 1) := hyp.q_pow_gt_p_pow
  have hgt : hyp.base.p ^ (hyp.base.q - 3) < hyp.base.q ^ (hyp.base.p - 3) := by
    by_contra hle
    rw [not_lt] at hle
    have e1 : hyp.base.q ^ (hyp.base.p + 1)
        = hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have e2 : hyp.base.p ^ (hyp.base.q + 1)
        = hyp.base.p ^ (hyp.base.q - 3) * hyp.base.p ^ 4 := by
      rw [← pow_add]; congr 1; omega
    have hq4p4 : hyp.base.q ^ 4 < hyp.base.p ^ 4 := Nat.pow_lt_pow_left hqp (by norm_num)
    have hppos : 0 < hyp.base.p ^ (hyp.base.q - 3) := pow_pos hp_prime.pos _
    have h1 : hyp.base.q ^ (hyp.base.p - 3) * hyp.base.q ^ 4
        ≤ hyp.base.p ^ (hyp.base.q - 3) * hyp.base.q ^ 4 := by gcongr
    have h2 : hyp.base.p ^ (hyp.base.q - 3) * hyp.base.q ^ 4
        < hyp.base.p ^ (hyp.base.q - 3) * hyp.base.p ^ 4 :=
      mul_lt_mul_of_pos_left hq4p4 hppos
    have hchain := lt_of_le_of_lt h1 h2
    rw [← e1, ← e2] at hchain
    omega
  -- Step 5: `q = 3`.
  have hq3 : hyp.base.q = 3 := by
    have hplt : hyp.base.p ^ (hyp.base.q - 3) < hyp.base.p ^ 2 := lt_trans hgt hqpm3
    have hexp : hyp.base.q - 3 < 2 := by
      by_contra hge
      rw [not_lt] at hge
      exact absurd hplt (not_lt.mpr (Nat.pow_le_pow_right (by omega) hge))
    rcases hyp.base.q_odd with ⟨k, hk⟩
    omega
  refine ⟨hq3, ?_⟩
  -- Step 6: `p = 5`.
  rw [hq3] at hqpm3
  by_contra hp_ne
  have hp7 : 7 ≤ hyp.base.p := by rcases hyp.base.p_odd with ⟨k, hk⟩; omega
  have := sq_le_three_pow_sub_three hp7
  omega

end Hypothesis

end OddOrder.Peterfalvi.S16
