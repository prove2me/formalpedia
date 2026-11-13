-- Prove2me | solution 1 for OddOrder.Peterfalvi.S16.cyclotomic_ratio_gt_of_q_lt_p
-- status  : ACCEPTED   (prove)
-- author  : @burkh4rt
-- created : 2026-11-12T16:30:58.890212+00:00
-- url     : https://prove2.me/submissions/0db81261-1954-4a14-a57d-ab4f3fa2acca

/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
-- From github.com/yawara/odd-order @ 20a6fccbb63c (Apache-2.0; LICENSE at that commit):
--   OddOrder/Peterfalvi/S16_NonExistenceG/KeyInequalityArithmetic.lean
-- Generated for Prove2Me by deleting declarations; the remaining commands are verbatim except:
-- `private` dropped where another file uses the declaration, and a solution's main theorem
-- renamed `_root_.solution` (platform convention).
import Definitions.Def_OddOrder_BG_AppC_LemmaC3_Step4Capstone
import Definitions.Def_OddOrder_Peterfalvi_S16_CoreLemmas

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

private theorem cyclotomic_quotient_sub_one_lt_div {p q : ℕ} (hp2 : 2 ≤ p) :
    (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) <
      (p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
  have hp_pos : 0 < p := lt_of_lt_of_le (by norm_num : 0 < 2) hp2
  have hp1_pos_nat : 0 < p - 1 := by omega
  have hden_pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by exact_mod_cast hp1_pos_nat
  have hdiv : p - 1 ∣ p ^ q - 1 := by
    simpa only [one_pow] using Nat.sub_dvd_pow_sub_pow p 1 q
  have hcast_div : (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) =
      ((p ^ q - 1 : ℕ) : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
    exact Nat.cast_div hdiv (ne_of_gt hden_pos)
  have hsub_le : (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) ≤
      (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) := by
    exact_mod_cast Nat.sub_le ((p ^ q - 1) / (p - 1)) 1
  have hnum_nat : p ^ q - 1 < p ^ q := by
    have hpq_pos : 0 < p ^ q := pow_pos hp_pos q
    omega
  have hnum : ((p ^ q - 1 : ℕ) : ℚ) < (p ^ q : ℚ) := by exact_mod_cast hnum_nat
  have hquot_lt : (((p ^ q - 1) / (p - 1) : ℕ) : ℚ) <
      (p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ)) := by
    rw [hcast_div]
    exact div_lt_div_of_pos_right hnum hden_pos
  exact lt_of_le_of_lt hsub_le hquot_lt

/-- Arithmetic bridge for Peterfalvi (14.8) under q < p. -/
theorem _root_.solution {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hpodd : Odd p) (hqodd : Odd q) (hqp : q < p) :
    (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) / (p : ℚ) >
      (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) / (q : ℚ) := by
  have hpow : q ^ (p + 1) > p ^ (q + 1) :=
    OddOrder.Peterfalvi.S16.q_pow_gt_p_pow hq hpodd hqodd hqp
  have hq2 : 2 ≤ q := hq.two_le
  have hp2 : 2 ≤ p := hp.two_le
  have hqpos_nat : 0 < q := hq.pos
  have hppos_nat : 0 < p := hp.pos
  have hqpos : (0 : ℚ) < q := by exact_mod_cast hqpos_nat
  have hppos : (0 : ℚ) < p := by exact_mod_cast hppos_nat
  have hp1_pos_nat : 0 < p - 1 := by omega
  have hp1pos : (0 : ℚ) < (((p - 1 : ℕ) : ℚ)) := by exact_mod_cast hp1_pos_nat
  have hp_pred_ge_q : q ≤ p - 1 := by omega
  have hmain_nat : p ^ (q + 1) < (p - 1) * q ^ p := by
    have hmul : q ^ (p + 1) ≤ (p - 1) * q ^ p := by
      rw [pow_succ, mul_comm (q ^ p) q]
      exact Nat.mul_le_mul_right (q ^ p) hp_pred_ge_q
    exact lt_of_lt_of_le hpow hmul
  have hmain : (p : ℚ) ^ (q + 1) < (((p - 1 : ℕ) : ℚ)) * (q : ℚ) ^ p := by
    exact_mod_cast hmain_nat
  have hmain' : (p ^ q : ℚ) * (p : ℚ) <
      (q ^ (p - 1) : ℚ) * ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) := by
    have hp_pow : (p : ℚ) ^ (q + 1) = (p : ℚ) ^ q * (p : ℚ) := by
      rw [pow_succ]
    have hq_pow : (q : ℚ) ^ p = (q : ℚ) ^ (p - 1) * (q : ℚ) := by
      calc
        (q : ℚ) ^ p = (q : ℚ) ^ ((p - 1) + 1) := by
          exact congrArg (fun n : ℕ => (q : ℚ) ^ n) (by omega : p = (p - 1) + 1)
        _ = (q : ℚ) ^ (p - 1) * (q : ℚ) := by rw [pow_succ]
    nlinarith
  have hleft_lower := cyclotomic_quotient_sub_one_ge_pow_pred (q := q) (p := p) hq2 hp2
  have hright_upper := cyclotomic_quotient_sub_one_lt_div (p := p) (q := q) hp2
  have hcompare_core : (p ^ q : ℚ) / ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) <
      (q ^ (p - 1) : ℚ) / (p : ℚ) := by
    rw [div_lt_div_iff₀]
    · simpa [Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm] using hmain'
    · positivity
    · exact hppos
  calc
    (((p ^ q - 1) / (p - 1) - 1 : ℕ) : ℚ) / (q : ℚ)
        < ((p ^ q : ℚ) / (((p - 1 : ℕ) : ℚ))) / (q : ℚ) :=
          div_lt_div_of_pos_right hright_upper hqpos
    _ = (p ^ q : ℚ) / ((q : ℚ) * (((p - 1 : ℕ) : ℚ))) := by
          field_simp [hqpos.ne', hp1pos.ne']
    _ < (q ^ (p - 1) : ℚ) / (p : ℚ) := hcompare_core
    _ ≤ (((q ^ p - 1) / (q - 1) - 1 : ℕ) : ℚ) / (p : ℚ) := by
          exact div_le_div_of_nonneg_right (by simpa [Nat.cast_pow] using hleft_lower)
            (le_of_lt hppos)

end OddOrder.Peterfalvi.S16
