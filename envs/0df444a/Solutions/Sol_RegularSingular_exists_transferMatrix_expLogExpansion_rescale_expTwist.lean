-- Prove2me | solution 1 for RegularSingular.exists_transferMatrix_expLogExpansion_rescale_expTwist
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:13.230386+00:00
-- url     : https://prove2.me/submissions/4d57c01c-a34f-5b42-a57e-f1b066387633

import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_RegularSingular_exists_transferMatrix_expLogExpansion_rescale_expTwist

set_option autoImplicit false

section GenericLemmas

open Finset Filter Topology

private theorem norm_exp_sub_sum_le (a : ℂ) (K : ℕ) (hK : ‖a‖ / (K + 1) ≤ 1 / 2) (y : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
    ‖Complex.exp (a * y) - ∑ k ∈ range K, (a * y) ^ k / (k.factorial : ℂ)‖ ≤
      ‖a‖ ^ K / (K.factorial : ℝ) * 2 * y ^ K := by
  have hy0 : 0 ≤ y := hy.1.le
  have hnorm : ‖a * (y : ℂ)‖ = ‖a‖ * y := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hy0]
  have hx : ‖a * (y : ℂ)‖ / (K.succ : ℝ) ≤ 1 / 2 := by
    rw [hnorm]
    have h1 : ‖a‖ * y ≤ ‖a‖ := by
      calc ‖a‖ * y ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hy.2 (norm_nonneg _)
        _ = ‖a‖ := mul_one _
    calc ‖a‖ * y / (K.succ : ℝ) ≤ ‖a‖ / (K.succ : ℝ) := by gcongr
      _ = ‖a‖ / ((K : ℝ) + 1) := by push_cast; rfl
      _ ≤ 1 / 2 := hK
  have h := Complex.exp_bound' hx
  calc ‖Complex.exp (a * y) - ∑ k ∈ range K, (a * y) ^ k / (k.factorial : ℂ)‖
      ≤ ‖a * (y : ℂ)‖ ^ K / (K.factorial : ℝ) * 2 := h
    _ = ‖a‖ ^ K / (K.factorial : ℝ) * 2 * y ^ K := by rw [hnorm, mul_pow]; ring

private theorem rpow_mul_abs_log_pow_le (δ : ℝ) (hδ : 0 < δ) (j : ℕ) (y : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
    y ^ δ * |Real.log y| ^ j ≤ ((j + 1) / δ) ^ j := by
  have hy0 : 0 < y := hy.1
  have hy1 : y ≤ 1 := hy.2
  set ε : ℝ := δ / (j + 1) with hε
  have hε0 : 0 < ε := by positivity

  have hlog : |Real.log y| ≤ y ^ (-ε) / ε := by
    have h1 : |Real.log y| = Real.log (1 / y) := by
      rw [Real.log_div one_ne_zero hy0.ne', Real.log_one, zero_sub, abs_of_nonpos (Real.log_nonpos hy0.le hy1)]
    rw [h1]
    have h2 := Real.log_le_rpow_div (by positivity : (0 : ℝ) ≤ 1 / y) hε0
    calc Real.log (1 / y) ≤ (1 / y) ^ ε / ε := h2
      _ = y ^ (-ε) / ε := by rw [one_div, Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le]
  have hlogpow : |Real.log y| ^ j ≤ (y ^ (-ε) / ε) ^ j :=
    pow_le_pow_left₀ (abs_nonneg _) hlog j
  have hyε : 0 ≤ y ^ (-ε) := Real.rpow_nonneg hy0.le _
  calc y ^ δ * |Real.log y| ^ j ≤ y ^ δ * (y ^ (-ε) / ε) ^ j :=
        mul_le_mul_of_nonneg_left hlogpow (Real.rpow_nonneg hy0.le _)
    _ = y ^ (δ - j * ε) * (1 / ε) ^ j := by
        rw [div_pow, ← Real.rpow_mul_natCast hy0.le, one_div, inv_pow, div_eq_mul_inv, ← mul_assoc,
          ← Real.rpow_add hy0]
        congr 1
        congr 1
        ring
    _ ≤ 1 * (1 / ε) ^ j := by
        gcongr
        · exact (Real.rpow_le_one hy0.le hy1 (by rw [hε]; field_simp; nlinarith [hδ])).trans le_rfl
    _ = ((j + 1) / δ) ^ j := by rw [one_mul, hε, one_div_div]

private theorem mul_abs_log_pow_le (j : ℕ) (y : ℝ) (hy : y ∈ Set.Ioc (0 : ℝ) 1) :
    y * |Real.log y| ^ j ≤ ((j : ℝ) + 1) ^ j := by
  have h := rpow_mul_abs_log_pow_le 1 one_pos j y hy
  rw [Real.rpow_one, div_one] at h
  exact h

private theorem cpow_add_natCast_mul (z : ℂ) (k : ℕ) (y : ℝ) (hy : 0 < y) :
    (y : ℂ) ^ (z + k) = (y : ℂ) ^ z * (y : ℂ) ^ k := by
  rw [Complex.cpow_add _ _ (by exact_mod_cast hy.ne'), Complex.cpow_natCast]

private theorem expansion_mul_exp {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (c : Fin n → Fin J → ℂ) (M : ℝ) (hM : ∀ i j, ‖c i j‖ ≤ M)
    (F : ℝ → ℂ) (C : ℝ)
    (hexp : ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y - ∑ i : Fin n, ∑ j : Fin J, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        C * y ^ (ρ + δ))
    (a : ℂ) (K : ℕ) (hK1 : ‖a‖ / (K + 1) ≤ 1 / 2) (hK2 : ∀ i, ρ + δ + 1 ≤ (e i).re + K) :
    ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖Complex.exp (a * y) * F y -
          ∑ i' : Fin n, ∑ j : Fin J,
            (∑ i : Fin n, ∑ k ∈ range K, if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
              ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        (Real.exp ‖a‖ * C +
          (‖a‖ ^ K / (K.factorial : ℝ) * 2 * M) * ∑ _i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ) +
          (M * Real.exp ‖a‖) * ∑ _i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) * y ^ (ρ + δ) := by
  classical
  intro y hy
  have hy0 : 0 < y := hy.1
  have hy1 : y ≤ 1 := hy.2
  have hyc : (y : ℂ) ≠ 0 := by exact_mod_cast hy0.ne'

  set S : ℂ := ∑ i : Fin n, ∑ j : Fin J, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) with hS
  set T : ℂ := ∑ k ∈ range K, (a * y) ^ k / (k.factorial : ℂ) with hT

  have key : Complex.exp (a * y) * F y -
      ∑ i' : Fin n, ∑ j : Fin J,
        (∑ i : Fin n, ∑ k ∈ range K, if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
          ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) =
      Complex.exp (a * y) * (F y - S) + (Complex.exp (a * y) - T) * S +
        (T * S - ∑ i' : Fin n, ∑ j : Fin J,
          (∑ i : Fin n, ∑ k ∈ range K, if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
            ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))) := by ring
  rw [key]

  have hφnorm : ∀ (z : ℂ) (j : ℕ), ‖(y : ℂ) ^ z * ((Real.log y : ℝ) : ℂ) ^ j‖ = y ^ z.re * |Real.log y| ^ j := by
    intro z j
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hyρδ : 0 ≤ y ^ (ρ + δ) := Real.rpow_nonneg hy0.le _

  have hA : ‖Complex.exp (a * y) * (F y - S)‖ ≤ Real.exp ‖a‖ * C * y ^ (ρ + δ) := by
    rw [norm_mul, Complex.norm_exp, mul_assoc]
    have h1 : Real.exp (a * (y : ℂ)).re ≤ Real.exp ‖a‖ := by
      apply Real.exp_le_exp.2
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
      calc a.re * y ≤ ‖a‖ * y := mul_le_mul_of_nonneg_right (Complex.re_le_norm a) hy0.le
        _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hy1 (norm_nonneg _)
        _ = ‖a‖ := mul_one _
    have h2 : ‖F y - S‖ ≤ C * y ^ (ρ + δ) := by rw [hS]; exact hexp y hy
    exact mul_le_mul h1 h2 (norm_nonneg _) (Real.exp_nonneg _)

  have hB : ‖(Complex.exp (a * y) - T) * S‖ ≤
      (‖a‖ ^ K / (K.factorial : ℝ) * 2 * M) * (∑ i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ)) *
        y ^ (ρ + δ) := by
    rw [norm_mul]
    have h1 := norm_exp_sub_sum_le a K hK1 y hy
    have hSle : ‖S‖ ≤ ∑ i : Fin n, ∑ j : Fin J, M * (y ^ (e i).re * |Real.log y| ^ (j : ℕ)) := by
      rw [hS]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
      rw [norm_mul, hφnorm]
      exact mul_le_mul_of_nonneg_right (hM i j) (by positivity)
    have hyK : 0 ≤ y ^ K := pow_nonneg hy0.le _
    have hc0 : 0 ≤ ‖a‖ ^ K / (K.factorial : ℝ) * 2 := by positivity
    calc ‖Complex.exp (a * y) - T‖ * ‖S‖
        ≤ (‖a‖ ^ K / (K.factorial : ℝ) * 2 * y ^ K) *
          ∑ i : Fin n, ∑ j : Fin J, M * (y ^ (e i).re * |Real.log y| ^ (j : ℕ)) :=
          mul_le_mul h1 hSle (norm_nonneg _) (by positivity)
      _ = (‖a‖ ^ K / (K.factorial : ℝ) * 2) *
          ∑ i : Fin n, ∑ j : Fin J, M * (y ^ K * y ^ (e i).re * |Real.log y| ^ (j : ℕ)) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun j _ => ?_
          ring
      _ ≤ (‖a‖ ^ K / (K.factorial : ℝ) * 2) *
          ∑ i : Fin n, ∑ j : Fin J, M * (((j : ℝ) + 1) ^ (j : ℕ) * y ^ (ρ + δ)) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_) hc0
          have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i j)
          refine mul_le_mul_of_nonneg_left ?_ hM0
          have hK2' := hK2 i
          have hpow : y ^ K * y ^ (e i).re = y ^ ((e i).re + K) := by
            rw [Real.rpow_add hy0, Real.rpow_natCast, mul_comm]
          have hle : y ^ ((e i).re + K) ≤ y ^ (ρ + δ + 1) :=
            Real.rpow_le_rpow_of_exponent_ge hy0 hy1 hK2'
          have hsplit : y ^ (ρ + δ + 1) = y ^ (ρ + δ) * y := by rw [Real.rpow_add hy0, Real.rpow_one]
          calc y ^ K * y ^ (e i).re * |Real.log y| ^ (j : ℕ)
              ≤ y ^ (ρ + δ + 1) * |Real.log y| ^ (j : ℕ) := by
                rw [hpow]; exact mul_le_mul_of_nonneg_right hle (by positivity)
            _ = y ^ (ρ + δ) * (y * |Real.log y| ^ (j : ℕ)) := by rw [hsplit]; ring
            _ ≤ y ^ (ρ + δ) * ((j : ℝ) + 1) ^ (j : ℕ) :=
                mul_le_mul_of_nonneg_left (mul_abs_log_pow_le j y hy) hyρδ
            _ = ((j : ℝ) + 1) ^ (j : ℕ) * y ^ (ρ + δ) := mul_comm _ _
      _ = (‖a‖ ^ K / (K.factorial : ℝ) * 2 * M) * (∑ i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ)) *
          y ^ (ρ + δ) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring

  set SUMP : ℂ := ∑ i' : Fin n, ∑ j : Fin J,
    (∑ i : Fin n, ∑ k ∈ range K, if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
      ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) with hSUMP
  have hC : ‖T * S - SUMP‖ ≤
      (M * Real.exp ‖a‖) * (∑ i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) * y ^ (ρ + δ) := by

    have hTS : T * S = ∑ i : Fin n, ∑ k ∈ range K, ∑ j : Fin J,
        c i j * (a ^ k / (k.factorial : ℂ)) * ((y : ℂ) ^ (e i + k) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) := by
      rw [hT, hS, Finset.sum_mul_sum, Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [cpow_add_natCast_mul (e i) k y hy0, mul_pow]
      ring

    have hcol : ∀ (i : Fin n) (k : ℕ) (j : Fin J),
        ∑ i' : Fin n, (if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
          ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) =
        if (e i + k).re ≤ ρ then
          c i j * (a ^ k / (k.factorial : ℂ)) * ((y : ℂ) ^ (e i + k) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))
        else 0 := by
      intro i k j
      by_cases hP : (e i + k).re ≤ ρ
      · obtain ⟨i₀, hi₀⟩ := hcl i k hP
        rw [if_pos hP, Finset.sum_eq_single i₀]
        · rw [if_pos hi₀.symm, hi₀]
        · intro i' _ hne
          rw [if_neg, zero_mul]
          intro h
          exact hne (he (h.symm.trans hi₀.symm))
        · intro h
          exact absurd (Finset.mem_univ i₀) h
      · rw [if_neg hP]
        refine Finset.sum_eq_zero fun i' _ => ?_
        rw [if_neg, zero_mul]
        intro h
        exact hP (by rw [h]; exact hre i')

    have hSUM : SUMP = ∑ i : Fin n, ∑ k ∈ range K, ∑ j : Fin J,
        if (e i + k).re ≤ ρ then
          c i j * (a ^ k / (k.factorial : ℂ)) * ((y : ℂ) ^ (e i + k) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))
        else 0 := by
      rw [hSUMP]
      simp only [Finset.sum_mul]
      calc ∑ i' : Fin n, ∑ j : Fin J, ∑ i : Fin n, ∑ k ∈ range K,
            (if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
              ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))
          = ∑ i' : Fin n, ∑ i : Fin n, ∑ j : Fin J, ∑ k ∈ range K,
            (if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
              ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ i : Fin n, ∑ i' : Fin n, ∑ j : Fin J, ∑ k ∈ range K,
            (if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
              ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) := Finset.sum_comm
        _ = ∑ i : Fin n, ∑ i' : Fin n, ∑ k ∈ range K, ∑ j : Fin J,
            (if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
              ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ i : Fin n, ∑ k ∈ range K, ∑ i' : Fin n, ∑ j : Fin J,
            (if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
              ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = ∑ i : Fin n, ∑ k ∈ range K, ∑ j : Fin J, ∑ i' : Fin n,
            (if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0) *
              ((y : ℂ) ^ e i' * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) :=
            Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
        _ = _ := Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
            Finset.sum_congr rfl fun j _ => hcol i k j

    rw [hTS, hSUM]
    simp only [← Finset.sum_sub_distrib]
    have hterm : ∀ (i : Fin n) (k : ℕ) (j : Fin J),
        ‖c i j * (a ^ k / (k.factorial : ℂ)) * ((y : ℂ) ^ (e i + k) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) -
          (if (e i + k).re ≤ ρ then
            c i j * (a ^ k / (k.factorial : ℂ)) * ((y : ℂ) ^ (e i + k) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))
          else 0)‖ ≤
        M * (‖a‖ ^ k / (k.factorial : ℝ)) * ((((j : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ)) := by
      intro i k j
      have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i j)
      by_cases hP : (e i + k).re ≤ ρ
      · rw [if_pos hP, sub_self, norm_zero]
        positivity
      · rw [if_neg hP, sub_zero]
        have hg := hgap i k (not_le.1 hP)
        rw [norm_mul, norm_mul, norm_div, norm_pow, Complex.norm_natCast, hφnorm]
        have h1 : y ^ (e i + k).re ≤ y ^ (ρ + 2 * δ) := Real.rpow_le_rpow_of_exponent_ge hy0 hy1 hg
        have h2 : y ^ (ρ + 2 * δ) = y ^ (ρ + δ) * y ^ δ := by
          rw [← Real.rpow_add hy0]; ring_nf
        have h3 := rpow_mul_abs_log_pow_le δ hδ j y hy
        calc ‖c i j‖ * (‖a‖ ^ k / (k.factorial : ℝ)) * (y ^ (e i + k).re * |Real.log y| ^ (j : ℕ))
            ≤ M * (‖a‖ ^ k / (k.factorial : ℝ)) * (y ^ (ρ + 2 * δ) * |Real.log y| ^ (j : ℕ)) := by
              gcongr
              exact hM i j
          _ = M * (‖a‖ ^ k / (k.factorial : ℝ)) * (y ^ (ρ + δ) * (y ^ δ * |Real.log y| ^ (j : ℕ))) := by
              rw [h2]; ring
          _ ≤ M * (‖a‖ ^ k / (k.factorial : ℝ)) * (y ^ (ρ + δ) * (((j : ℝ) + 1) / δ) ^ (j : ℕ)) := by
              gcongr
          _ = M * (‖a‖ ^ k / (k.factorial : ℝ)) * ((((j : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ)) := by ring
    have hexpsum : ∑ k ∈ range K, ‖a‖ ^ k / (k.factorial : ℝ) ≤ Real.exp ‖a‖ :=
      Real.sum_le_exp_of_nonneg (norm_nonneg a) K
    calc ‖∑ i : Fin n, ∑ k ∈ range K, ∑ j : Fin J,
          (c i j * (a ^ k / (k.factorial : ℂ)) * ((y : ℂ) ^ (e i + k) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ)) -
            if (e i + k).re ≤ ρ then
              c i j * (a ^ k / (k.factorial : ℂ)) * ((y : ℂ) ^ (e i + k) * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))
            else 0)‖
        ≤ ∑ i : Fin n, ∑ k ∈ range K, ∑ j : Fin J,
          M * (‖a‖ ^ k / (k.factorial : ℝ)) * ((((j : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ)) :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => (norm_sum_le _ _).trans
            (Finset.sum_le_sum fun k _ => (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i k j)))
      _ = ∑ i : Fin n, ∑ j : Fin J, (∑ k ∈ range K, ‖a‖ ^ k / (k.factorial : ℝ)) *
          (M * ((((j : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
      _ ≤ ∑ i : Fin n, ∑ j : Fin J, Real.exp ‖a‖ * (M * ((((j : ℝ) + 1) / δ) ^ (j : ℕ) * y ^ (ρ + δ))) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM i j)
          exact mul_le_mul_of_nonneg_right hexpsum (by positivity)
      _ = (M * Real.exp ‖a‖) * (∑ i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) * y ^ (ρ + δ) := by
          simp only [Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
          ring
  calc ‖Complex.exp (a * y) * (F y - S) + (Complex.exp (a * y) - T) * S + (T * S - SUMP)‖
      ≤ ‖Complex.exp (a * y) * (F y - S)‖ + ‖(Complex.exp (a * y) - T) * S‖ + ‖T * S - SUMP‖ :=
        (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ ≤ _ := add_le_add (add_le_add hA hB) hC
    _ = _ := by ring

private theorem rescale_expansion {n J : ℕ} (e : Fin n → ℂ) (c : Fin n → Fin J → ℂ) (lam : ℝ) (hlam : 0 < lam)
    (y : ℝ) (hy : 0 < y) :
    ∑ i : Fin n, ∑ j : Fin J,
        c i j * (((lam * y : ℝ) : ℂ) ^ e i * ((Real.log (lam * y) : ℝ) : ℂ) ^ (j : ℕ)) =
      ∑ i : Fin n, ∑ k : Fin J,
        (∑ m : Fin J, if (k : ℕ) ≤ (m : ℕ) then
            c i m * ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) *
              (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ)
          else 0) * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (k : ℕ)) := by
  classical
  refine Finset.sum_congr rfl fun i _ => ?_

  have hpow : ((lam * y : ℝ) : ℂ) ^ e i = ((lam : ℝ) : ℂ) ^ e i * (y : ℂ) ^ e i := by
    rw [Complex.ofReal_mul]
    exact Complex.mul_cpow_ofReal_nonneg hlam.le hy.le (e i)
  have hlog : ((Real.log (lam * y) : ℝ) : ℂ) = ((Real.log y : ℝ) : ℂ) + ((Real.log lam : ℝ) : ℂ) := by
    rw [Real.log_mul hlam.ne' hy.ne', add_comm]
    push_cast
    ring

  have hL : ∀ m : Fin J, c i m * (((lam * y : ℝ) : ℂ) ^ e i * ((Real.log (lam * y) : ℝ) : ℂ) ^ (m : ℕ)) =
      ∑ k : Fin J, (if (k : ℕ) ≤ (m : ℕ) then
          c i m * ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) *
            (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ)
        else 0) * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (k : ℕ)) := by
    intro m
    rw [hpow, hlog, add_pow]

    have hidx : ∀ f : ℕ → ℂ, ∑ k ∈ Finset.range ((m : ℕ) + 1), f k =
        ∑ k : Fin J, if (k : ℕ) ≤ (m : ℕ) then f k else 0 := by
      intro f
      rw [Fin.sum_univ_eq_sum_range (fun k => if k ≤ (m : ℕ) then f k else 0) J, ← Finset.sum_filter]
      have hfil : (Finset.range J).filter (fun k => k ≤ (m : ℕ)) = Finset.range ((m : ℕ) + 1) := by
        ext k
        simp only [Finset.mem_filter, Finset.mem_range]
        have := m.2
        omega
      rw [hfil]
    rw [Finset.mul_sum, Finset.mul_sum, hidx]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : (k : ℕ) ≤ (m : ℕ)
    · simp only [if_pos hk]
      ring
    · simp only [if_neg hk]
      ring
  rw [Finset.sum_congr rfl fun m _ => hL m, Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_mul]

private theorem expansion_extend {n J : ℕ} (e : Fin n → ℂ) (θ : ℝ) (s : ℝ) (hs0 : 0 < s) (hs1 : s ≤ 1)
    (F : ℝ → ℂ) (c : Fin n → Fin J → ℂ) (C M₁ M₂ : ℝ) (hM₂ : ∀ i j, ‖c i j‖ ≤ M₂)
    (hexp : ∀ y ∈ Set.Ioc (0 : ℝ) s,
      ‖F y - ∑ i : Fin n, ∑ j : Fin J, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ C * y ^ θ)
    (hF : ∀ y ∈ Set.Icc s 1, ‖F y‖ ≤ M₁) :
    ∀ y ∈ Set.Ioc (0 : ℝ) 1,
      ‖F y - ∑ i : Fin n, ∑ j : Fin J, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        max C ((M₁ + M₂ * ∑ i : Fin n, ∑ j : Fin J, max (s ^ (e i).re) 1 * |Real.log s| ^ (j : ℕ)) /
          min (s ^ θ) 1) * y ^ θ := by
  classical

  set P : ℝ := ∑ i : Fin n, ∑ j : Fin J, max (s ^ (e i).re) 1 * |Real.log s| ^ (j : ℕ) with hP
  have hsum : ∀ y ∈ Set.Icc s 1,
      ‖∑ i : Fin n, ∑ j : Fin J, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤ M₂ * P := by
    intro y hy
    have hy0 : 0 < y := hs0.trans_le hy.1
    have hlog : |Real.log y| ≤ |Real.log s| := by
      rw [abs_of_nonpos (Real.log_nonpos hy0.le hy.2), abs_of_nonpos (Real.log_nonpos hs0.le hs1)]
      linarith [Real.log_le_log hs0 hy.1]
    rw [hP, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy0, norm_pow, Complex.norm_real,
      Real.norm_eq_abs]
    have h1 : y ^ (e i).re ≤ max (s ^ (e i).re) 1 := by
      rcases le_or_gt 0 (e i).re with hre | hre
      · exact (Real.rpow_le_one hy0.le hy.2 hre).trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos hs0 hy.1 hre.le).trans (le_max_left _ _)
    have h2 : |Real.log y| ^ (j : ℕ) ≤ |Real.log s| ^ (j : ℕ) := pow_le_pow_left₀ (abs_nonneg _) hlog _
    have hM₂0 : 0 ≤ M₂ := (norm_nonneg _).trans (hM₂ i j)
    calc ‖c i j‖ * (y ^ (e i).re * |Real.log y| ^ (j : ℕ))
        ≤ M₂ * (max (s ^ (e i).re) 1 * |Real.log s| ^ (j : ℕ)) :=
          mul_le_mul (hM₂ i j) (mul_le_mul h1 h2 (by positivity) (by positivity)) (by positivity) hM₂0
      _ = _ := by ring

  set m : ℝ := min (s ^ θ) 1 with hm
  have hmpos : 0 < m := lt_min (Real.rpow_pos_of_pos hs0 θ) one_pos
  intro y hy
  have hy0 : 0 < y := hy.1
  have hyθ : 0 ≤ y ^ θ := Real.rpow_nonneg hy0.le θ
  rcases le_or_gt y s with hys | hys
  · exact (hexp y ⟨hy0, hys⟩).trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hyθ)
  · have hyI : y ∈ Set.Icc s 1 := ⟨hys.le, hy.2⟩
    have hmy : m ≤ y ^ θ := by
      rcases le_or_gt 0 θ with hθ | hθ
      · exact (min_le_left _ _).trans (Real.rpow_le_rpow hs0.le hys.le hθ)
      · exact (min_le_right _ _).trans (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hy0 hy.2 hθ.le)
    calc _ ≤ ‖F y‖ + ‖∑ i : Fin n, ∑ j : Fin J, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ :=
          norm_sub_le _ _
      _ ≤ M₁ + M₂ * P := add_le_add (hF y hyI) (hsum y hyI)
      _ = (M₁ + M₂ * P) / m * m := by field_simp
      _ ≤ (M₁ + M₂ * P) / m * y ^ θ := by
          gcongr
          have : 0 ≤ M₁ + M₂ * P := by
            have := (norm_nonneg _).trans (hF y hyI)
            have := (norm_nonneg _).trans (hsum y hyI)
            linarith
          positivity
      _ ≤ max C ((M₁ + M₂ * P) / m) * y ^ θ := mul_le_mul_of_nonneg_right (le_max_right _ _) hyθ

private theorem rescale_coeff_bound {n J : ℕ} (e : Fin n → ℂ) (c : Fin n → Fin J → ℂ) (M : ℝ) (hM : ∀ i j, ‖c i j‖ ≤ M)
    (hM0 : 0 ≤ M) (lam : ℝ) (hlam : 0 < lam) (i : Fin n) (k : Fin J) :
    ‖∑ m : Fin J, if (k : ℕ) ≤ (m : ℕ) then
        c i m * ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) *
          (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ)
      else 0‖ ≤ M * lam ^ (e i).re * ((J : ℝ) * (1 + |Real.log lam|) ^ J * 2 ^ J) := by
  classical
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ m : Fin J, ‖(if (k : ℕ) ≤ (m : ℕ) then
      c i m * ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) *
        (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ) else 0)‖ ≤ M * lam ^ (e i).re * ((1 + |Real.log lam|) ^ J * 2 ^ J) := by
    intro m
    split_ifs with hkm
    · rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hlam, norm_pow, Complex.norm_real,
        Real.norm_eq_abs, Complex.norm_natCast]
      have h1 : |Real.log lam| ^ ((m : ℕ) - (k : ℕ)) ≤ (1 + |Real.log lam|) ^ J := by
        calc |Real.log lam| ^ ((m : ℕ) - (k : ℕ)) ≤ (1 + |Real.log lam|) ^ ((m : ℕ) - (k : ℕ)) :=
              pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log lam)]) _
          _ ≤ (1 + |Real.log lam|) ^ J :=
              pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log lam)]) (by omega)
      have h2 : (((m : ℕ).choose (k : ℕ) : ℕ) : ℝ) ≤ 2 ^ J := by
        calc (((m : ℕ).choose (k : ℕ) : ℕ) : ℝ) ≤ ((2 ^ (m : ℕ) : ℕ) : ℝ) := by
              exact_mod_cast Nat.choose_le_two_pow (m : ℕ) (k : ℕ)
          _ ≤ 2 ^ J := by
              push_cast
              exact pow_le_pow_right₀ (by norm_num) (by omega)
      have hlr : 0 ≤ lam ^ (e i).re := by positivity
      calc ‖c i m‖ * lam ^ (e i).re * |Real.log lam| ^ ((m : ℕ) - (k : ℕ)) * (((m : ℕ).choose (k : ℕ) : ℕ) : ℝ)
          ≤ M * lam ^ (e i).re * (1 + |Real.log lam|) ^ J * 2 ^ J :=
            mul_le_mul (mul_le_mul (mul_le_mul (hM i m) le_rfl hlr hM0) h1 (by positivity)
              (mul_nonneg hM0 hlr)) h2 (by positivity)
              (mul_nonneg (mul_nonneg hM0 hlr) (by positivity))
        _ = _ := by ring
    · rw [norm_zero]
      positivity
  calc ∑ m : Fin J, ‖(if (k : ℕ) ≤ (m : ℕ) then
        c i m * ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) *
          (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ) else 0)‖
      ≤ ∑ _m : Fin J, M * lam ^ (e i).re * ((1 + |Real.log lam|) ^ J * 2 ^ J) := Finset.sum_le_sum fun m _ => hterm m
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

private theorem exp_coeff_bound {n J : ℕ} (e : Fin n → ℂ) (c : Fin n → Fin J → ℂ) (M : ℝ) (hM : ∀ i j, ‖c i j‖ ≤ M)
    (hM0 : 0 ≤ M) (a : ℂ) (K : ℕ) (i' : Fin n) (j : Fin J) :
    ‖∑ i : Fin n, ∑ k ∈ range K, if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0‖ ≤
      (n : ℝ) * M * Real.exp ‖a‖ := by
  classical
  refine (norm_sum_le _ _).trans ?_
  have hinner : ∀ i : Fin n,
      ‖∑ k ∈ range K, if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0‖ ≤ M * Real.exp ‖a‖ := by
    intro i
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ range K, ‖(if e i + k = e i' then c i j * (a ^ k / (k.factorial : ℂ)) else 0)‖ ≤
        M * (‖a‖ ^ k / (k.factorial : ℝ)) := by
      intro k _
      split_ifs
      · rw [norm_mul, norm_div, norm_pow, Complex.norm_natCast]
        exact mul_le_mul_of_nonneg_right (hM i j) (by positivity)
      · rw [norm_zero]
        positivity
    calc _ ≤ ∑ k ∈ range K, M * (‖a‖ ^ k / (k.factorial : ℝ)) := Finset.sum_le_sum hterm
      _ = M * ∑ k ∈ range K, ‖a‖ ^ k / (k.factorial : ℝ) := by rw [Finset.mul_sum]
      _ ≤ M * Real.exp ‖a‖ := mul_le_mul_of_nonneg_left (Real.sum_le_exp_of_nonneg (norm_nonneg a) K) hM0
  calc _ ≤ ∑ _i : Fin n, M * Real.exp ‖a‖ := Finset.sum_le_sum fun i _ => hinner i
    _ = _ := by rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_assoc]

private theorem transferEntry_bound {n J : ℕ} (e : Fin n → ℂ) (lam₀ : ℝ) (hlam₀ : 0 < lam₀) (hlam₀1 : lam₀ ≤ 1)
    (aB : ℝ) (Kd : ℕ) (Ω' : ℝ) (hΩ' : 0 ≤ Ω') (κ₀ a' : ℂ) (hκ₀ : ‖κ₀‖ ≤ Ω') (ha' : ‖a'‖ ≤ aB)
    (lam : ℝ) (hlam : 0 < lam) (hlam_ge : lam₀ ≤ lam) (hlam_le : lam ≤ lam₀⁻¹)
    (i : Fin n) (k : Fin J) (i₀ : Fin n) (m : Fin J) :
    ‖κ₀ * (if (k : ℕ) ≤ (m : ℕ) then
        (∑ k' ∈ range Kd, if e i₀ + k' = e i then a' ^ k' / (k'.factorial : ℂ) else 0) *
          ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) * (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ)
      else 0)‖ ≤
      Ω' * (Real.exp aB * (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) *
        ((1 + |Real.log lam₀|) ^ J * 2 ^ J)) := by
  classical
  have hLAM0 : 0 ≤ ∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re)) :=
    Finset.sum_nonneg fun _ _ => add_nonneg (Real.rpow_nonneg hlam₀.le _) (Real.rpow_nonneg hlam₀.le _)
  have hR0 : 0 ≤ Real.exp aB * (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) *
      ((1 + |Real.log lam₀|) ^ J * 2 ^ J) := by positivity
  rw [norm_mul]
  refine mul_le_mul hκ₀ ?_ (norm_nonneg _) hΩ'
  split_ifs with hkm
  ·
    have hΛ : ‖∑ k' ∈ range Kd, if e i₀ + k' = e i then a' ^ k' / (k'.factorial : ℂ) else 0‖ ≤ Real.exp aB := by
      refine (norm_sum_le _ _).trans ?_
      have hterm : ∀ k' ∈ range Kd, ‖(if e i₀ + k' = e i then a' ^ k' / (k'.factorial : ℂ) else 0)‖ ≤
          ‖a'‖ ^ k' / (k'.factorial : ℝ) := by
        intro k' _
        split_ifs
        · rw [norm_div, norm_pow, Complex.norm_natCast]
        · rw [norm_zero]; positivity
      calc _ ≤ ∑ k' ∈ range Kd, ‖a'‖ ^ k' / (k'.factorial : ℝ) := Finset.sum_le_sum hterm
        _ ≤ Real.exp ‖a'‖ := Real.sum_le_exp_of_nonneg (norm_nonneg a') Kd
        _ ≤ Real.exp aB := Real.exp_le_exp.2 ha'

    have hlog_le : |Real.log lam| ≤ |Real.log lam₀| := by
      rw [abs_le]
      have h1 : Real.log lam₀ ≤ Real.log lam := Real.log_le_log hlam₀ hlam_ge
      have h2 : Real.log lam ≤ -Real.log lam₀ := by
        rw [← Real.log_inv]
        exact Real.log_le_log hlam hlam_le
      have h3 : Real.log lam₀ ≤ 0 := Real.log_nonpos hlam₀.le hlam₀1
      rw [abs_of_nonpos h3]
      constructor <;> linarith
    have hlamre : lam ^ (e i).re ≤ ∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re)) := by
      have hterm : lam ^ (e i).re ≤ lam₀ ^ (e i).re + lam₀ ^ (-(e i).re) := by
        rcases le_or_gt 0 (e i).re with hre' | hre'
        · have : lam ^ (e i).re ≤ (lam₀⁻¹) ^ (e i).re := Real.rpow_le_rpow hlam.le hlam_le hre'
          rw [Real.inv_rpow hlam₀.le, ← Real.rpow_neg hlam₀.le] at this
          linarith [Real.rpow_nonneg hlam₀.le (e i).re]
        · have : lam ^ (e i).re ≤ lam₀ ^ (e i).re := Real.rpow_le_rpow_of_nonpos hlam₀ hlam_ge hre'.le
          linarith [Real.rpow_nonneg hlam₀.le (-(e i).re)]
      exact hterm.trans (Finset.single_le_sum (f := fun i₁ => lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))
        (fun _ _ => by positivity) (Finset.mem_univ i))
    have h1 : |Real.log lam| ^ ((m : ℕ) - (k : ℕ)) ≤ (1 + |Real.log lam₀|) ^ J := by
      calc |Real.log lam| ^ ((m : ℕ) - (k : ℕ)) ≤ (1 + |Real.log lam₀|) ^ ((m : ℕ) - (k : ℕ)) :=
            pow_le_pow_left₀ (abs_nonneg _) (by linarith [abs_nonneg (Real.log lam)]) _
        _ ≤ (1 + |Real.log lam₀|) ^ J :=
            pow_le_pow_right₀ (by linarith [abs_nonneg (Real.log lam₀)]) (by omega)
    have h2 : (((m : ℕ).choose (k : ℕ) : ℕ) : ℝ) ≤ 2 ^ J := by
      calc (((m : ℕ).choose (k : ℕ) : ℕ) : ℝ) ≤ ((2 ^ (m : ℕ) : ℕ) : ℝ) := by
            exact_mod_cast Nat.choose_le_two_pow (m : ℕ) (k : ℕ)
        _ ≤ 2 ^ J := by
            push_cast
            exact pow_le_pow_right₀ (by norm_num) (by omega)
    rw [norm_mul, norm_mul, norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hlam, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, Complex.norm_natCast]
    have hlr : 0 ≤ lam ^ (e i).re := by positivity
    calc _ ≤ Real.exp aB * (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) *
          (1 + |Real.log lam₀|) ^ J * 2 ^ J :=
          mul_le_mul (mul_le_mul (mul_le_mul hΛ hlamre hlr (Real.exp_nonneg _)) h1 (by positivity)
            (mul_nonneg (Real.exp_nonneg _) hLAM0)) h2 (by positivity)
            (mul_nonneg (mul_nonneg (Real.exp_nonneg _) hLAM0) (by positivity))
      _ = _ := by ring
  · rw [norm_zero]
    exact hR0

end GenericLemmas

open Finset in
theorem solution
    {n J : ℕ} (e : Fin n → ℂ) (he : Function.Injective e) (ρ δ : ℝ) (hδ : 0 < δ)
    (hre : ∀ i, (e i).re ≤ ρ)
    (hcl : ∀ i (k : ℕ), (e i + k).re ≤ ρ → ∃ i', e i' = e i + k)
    (hgap : ∀ i (k : ℕ), ρ < (e i + k).re → ρ + 2 * δ ≤ (e i + k).re)
    (lam₀ : ℝ) (hlam₀ : 0 < lam₀) (hlam₀1 : lam₀ ≤ 1)
    (aB : ℝ) (Kd : ℕ) (hKd1 : aB / (Kd + 1) ≤ 1 / 2) (hKd2 : ∀ i, ρ + δ + 1 ≤ (e i).re + Kd)
    (Ω' : ℝ) (hΩ' : 0 ≤ Ω')
    (κ₀ a' : ℂ) (hκ₀ : ‖κ₀‖ ≤ Ω') (ha' : ‖a'‖ ≤ aB) (ha're : a'.re = 0)
    (lam : ℝ) (hlam : 0 < lam) (hlam_ge : lam₀ ≤ lam) (hlam_le : lam ≤ lam₀⁻¹) :
    ∃ L : Fin n → Fin J → Fin n → Fin J → ℂ,
      (∀ i k i₀ m, ‖L i k i₀ m‖ ≤ Ω' * (Real.exp aB *
        (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) * ((1 + |Real.log lam₀|) ^ J * 2 ^ J))) ∧
      ∀ (Bc' C₁' W₀ : ℝ), 0 ≤ Bc' → 0 ≤ C₁' → 0 ≤ W₀ →
      ∀ (G F : ℝ → ℂ) (c : Fin n → Fin J → ℂ), (∀ i j, ‖c i j‖ ≤ Bc') →
      (∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖G y - ∑ i : Fin n, ∑ j : Fin J, c i j * ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
          C₁' * y ^ (ρ + δ)) →
      (∀ s : ℝ, lam₀ ≤ s → s ≤ lam₀⁻¹ → ‖G s‖ ≤ W₀) →
      (∀ y : ℝ, 0 < y → F y = κ₀ * (Complex.exp (a' * ((lam * y : ℝ) : ℂ)) * G (lam * y))) →
      (∀ i k, ‖∑ i₀ : Fin n, ∑ m : Fin J, L i k i₀ m * c i₀ m‖ ≤
        Ω' * ((n : ℝ) * Bc' * Real.exp aB *
          (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) *
          ((J : ℝ) * (1 + |Real.log lam₀|) ^ J * 2 ^ J))) ∧
      ∀ y ∈ Set.Ioc (0 : ℝ) 1,
        ‖F y - ∑ i : Fin n, ∑ k : Fin J, (∑ i₀ : Fin n, ∑ m : Fin J, L i k i₀ m * c i₀ m) *
            ((y : ℂ) ^ e i * ((Real.log y : ℝ) : ℂ) ^ (k : ℕ))‖ ≤
          max (Ω' * (Real.exp aB * C₁' +
              (aB ^ Kd / (Kd.factorial : ℝ) * 2 * Bc') * ∑ _i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ) +
              (Bc' * Real.exp aB) * ∑ _i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ)) *
              max (lam₀ ^ (ρ + δ)) (lam₀ ^ (-(ρ + δ))))
            ((Ω' * W₀ + Ω' * ((n : ℝ) * Bc' * Real.exp aB *
                (∑ i₁ : Fin n, (lam₀ ^ (e i₁).re + lam₀ ^ (-(e i₁).re))) *
                ((J : ℝ) * (1 + |Real.log lam₀|) ^ J * 2 ^ J)) *
              ∑ i₁ : Fin n, ∑ j : Fin J, max (lam₀ ^ (e i₁).re) 1 * |Real.log lam₀| ^ (j : ℕ)) /
              min (lam₀ ^ (ρ + δ)) 1) * y ^ (ρ + δ) := by
  classical

  set Λc : Fin n → Fin n → ℂ := fun i i₀ =>
    ∑ k' ∈ range Kd, if e i₀ + k' = e i then a' ^ k' / (k'.factorial : ℂ) else 0 with hΛc
  set L : Fin n → Fin J → Fin n → Fin J → ℂ := fun i k i₀ m =>
    κ₀ * (if (k : ℕ) ≤ (m : ℕ) then
        Λc i i₀ * ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) *
          (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ)
      else 0) with hL
  refine ⟨L, fun i k i₀ m => ?_, ?_⟩
  · simp only [hL, hΛc]
    exact transferEntry_bound e lam₀ hlam₀ hlam₀1 aB Kd Ω' hΩ' κ₀ a' hκ₀ ha' lam hlam hlam_ge hlam_le i k i₀ m
  intro Bc' C₁' W₀ hBc'0 hC₁'0 hW₀0 G F c hcb hG hGW hW
  set LAM : ℝ := ∑ i : Fin n, (lam₀ ^ (e i).re + lam₀ ^ (-(e i).re)) with hLAM
  set M_D : ℝ := (n : ℝ) * Bc' * Real.exp aB with hM_D
  set C_D : ℝ := Real.exp aB * C₁' +
    (aB ^ Kd / (Kd.factorial : ℝ) * 2 * Bc') * ∑ i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ) +
    (Bc' * Real.exp aB) * ∑ i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ) with hC_D
  set JB : ℝ := (J : ℝ) * (1 + |Real.log lam₀|) ^ J * 2 ^ J with hJB
  set M_R : ℝ := M_D * LAM * JB with hM_R
  set Bfin : ℝ := Ω' * M_R with hBfin
  have hLAM0 : 0 ≤ LAM := Finset.sum_nonneg fun _ _ =>
    add_nonneg (Real.rpow_nonneg hlam₀.le _) (Real.rpow_nonneg hlam₀.le _)
  have hJB0 : 0 ≤ JB := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg (by positivity) _))
    (pow_nonneg (by norm_num) _)
  have hM_D0 : 0 ≤ M_D := mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hBc'0) (Real.exp_pos _).le
  have hBfin0 : 0 ≤ Bfin := mul_nonneg hΩ' (mul_nonneg (mul_nonneg hM_D0 hLAM0) hJB0)
  set LAMθ : ℝ := max (lam₀ ^ (ρ + δ)) (lam₀ ^ (-(ρ + δ))) with hLAMθ
  set P₀ : ℝ := ∑ i : Fin n, ∑ j : Fin J, max (lam₀ ^ (e i).re) 1 * |Real.log lam₀| ^ (j : ℕ) with hP₀
  set m₀ : ℝ := min (lam₀ ^ (ρ + δ)) 1 with hm₀
  have hm₀pos : 0 < m₀ := lt_min (Real.rpow_pos_of_pos hlam₀ _) one_pos
  have ha'0 : 0 ≤ ‖a'‖ := norm_nonneg _
  have haB0 : 0 ≤ aB := ha'0.trans ha'
  have hKd1' : ‖a'‖ / (Kd + 1) ≤ 1 / 2 :=
    (div_le_div_of_nonneg_right ha' (by positivity)).trans hKd1

  set cD : Fin n → Fin J → ℂ := fun i' j => ∑ i : Fin n, ∑ k ∈ Finset.range Kd,
    if e i + k = e i' then c i j * (a' ^ k / (k.factorial : ℂ)) else 0 with hcD
  set cR : Fin n → Fin J → ℂ := fun i k => ∑ m : Fin J, if (k : ℕ) ≤ (m : ℕ) then
    cD i m * ((lam : ℝ) : ℂ) ^ e i * ((Real.log lam : ℝ) : ℂ) ^ ((m : ℕ) - (k : ℕ)) *
      (((m : ℕ).choose (k : ℕ) : ℕ) : ℂ) else 0 with hcR
  have hLc : ∀ i k, ∑ i₀ : Fin n, ∑ m : Fin J, L i k i₀ m * c i₀ m = κ₀ * cR i k := by
    intro i k
    have hcDm : ∀ m : Fin J, cD i m = ∑ i₀ : Fin n, Λc i i₀ * c i₀ m := by
      intro m
      simp only [hcD, hΛc]
      refine Finset.sum_congr rfl fun i₀ _ => ?_
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun k' _ => ?_
      split_ifs <;> ring
    rw [Finset.sum_comm]
    simp only [hcR, hcDm]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hkm : (k : ℕ) ≤ (m : ℕ)
    · simp only [hL, if_pos hkm]
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i₀ _ => ?_
      ring
    · simp only [hL, if_neg hkm, mul_zero, zero_mul, Finset.sum_const_zero]
  have hcD_bound : ∀ i j, ‖cD i j‖ ≤ M_D := by
    intro i' j
    refine (exp_coeff_bound e c Bc' hcb hBc'0 a' Kd i' j).trans ?_
    rw [hM_D]
    gcongr
  have hlog_le : |Real.log lam| ≤ |Real.log lam₀| := by
    rw [abs_le]
    have h1 : Real.log lam₀ ≤ Real.log lam := Real.log_le_log hlam₀ hlam_ge
    have h2 : Real.log lam ≤ -Real.log lam₀ := by
      rw [← Real.log_inv]
      exact Real.log_le_log hlam hlam_le
    have h3 : Real.log lam₀ ≤ 0 := Real.log_nonpos hlam₀.le hlam₀1
    rw [abs_of_nonpos h3]
    constructor <;> linarith
  have hlamre : ∀ i, lam ^ (e i).re ≤ LAM := by
    intro i
    have hterm : lam ^ (e i).re ≤ lam₀ ^ (e i).re + lam₀ ^ (-(e i).re) := by
      rcases le_or_gt 0 (e i).re with hre' | hre'
      · have : lam ^ (e i).re ≤ (lam₀⁻¹) ^ (e i).re := Real.rpow_le_rpow hlam.le hlam_le hre'
        rw [Real.inv_rpow hlam₀.le, ← Real.rpow_neg hlam₀.le] at this
        linarith [Real.rpow_nonneg hlam₀.le (e i).re]
      · have : lam ^ (e i).re ≤ lam₀ ^ (e i).re := Real.rpow_le_rpow_of_nonpos hlam₀ hlam_ge hre'.le
        linarith [Real.rpow_nonneg hlam₀.le (-(e i).re)]
    exact hterm.trans (Finset.single_le_sum (f := fun i => lam₀ ^ (e i).re + lam₀ ^ (-(e i).re))
      (fun _ _ => by positivity) (Finset.mem_univ i))
  have hcR_bound : ∀ i k, ‖cR i k‖ ≤ M_R := by
    intro i k
    refine (rescale_coeff_bound e cD M_D hcD_bound hM_D0 lam hlam i k).trans ?_
    rw [hM_R, hJB]
    have h1 : (1 + |Real.log lam|) ^ J ≤ (1 + |Real.log lam₀|) ^ J :=
      pow_le_pow_left₀ (by positivity) (by linarith) J
    have h2 : 0 ≤ lam ^ (e i).re := by positivity
    exact mul_le_mul (mul_le_mul_of_nonneg_left (hlamre i) hM_D0)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 (by positivity)) (by positivity))
      (by positivity) (mul_nonneg hM_D0 (h2.trans (hlamre i)))
  have hvB : ∀ i k, ‖κ₀ * cR i k‖ ≤ Bfin := by
    intro i k
    rw [norm_mul, hBfin]
    exact mul_le_mul hκ₀ (hcR_bound i k) (norm_nonneg _) hΩ'
  refine ⟨fun i k => by rw [hLc]; exact hvB i k, ?_⟩

  have hD := expansion_mul_exp e he ρ δ hδ hre hcl hgap c Bc' hcb G C₁' hG a' Kd hKd1' hKd2
  have hCD_mono : Real.exp ‖a'‖ * C₁' +
      (‖a'‖ ^ Kd / (Kd.factorial : ℝ) * 2 * Bc') * ∑ i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ) +
      (Bc' * Real.exp ‖a'‖) * ∑ i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ) ≤ C_D := by
    have hexp_le : Real.exp ‖a'‖ ≤ Real.exp aB := Real.exp_le_exp.2 ha'
    have hpow_le : ‖a'‖ ^ Kd ≤ aB ^ Kd := pow_le_pow_left₀ ha'0 ha' Kd
    have hS1 : 0 ≤ ∑ i : Fin n, ∑ j : Fin J, ((j : ℝ) + 1) ^ (j : ℕ) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    have hS2 : 0 ≤ ∑ i : Fin n, ∑ j : Fin J, (((j : ℝ) + 1) / δ) ^ (j : ℕ) :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
    rw [hC_D]
    gcongr

  set s : ℝ := min 1 lam⁻¹ with hs
  have hs0 : 0 < s := lt_min one_pos (inv_pos.2 hlam)
  have hs1 : s ≤ 1 := min_le_left _ _
  have hs_lam : lam₀ ≤ s := by
    refine le_min hlam₀1 ?_
    rw [le_inv_comm₀ hlam₀ hlam]
    exact hlam_le

  have hsmall : ∀ y₁ ∈ Set.Ioc (0 : ℝ) s,
      ‖F y₁ -
        ∑ i : Fin n, ∑ j : Fin J, κ₀ * cR i j * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ))‖ ≤
        Ω' * C_D * LAMθ * y₁ ^ (ρ + δ) := by
    intro y₁ hy₁
    have hy₁0 : 0 < y₁ := hy₁.1
    have hly : lam * y₁ ∈ Set.Ioc (0 : ℝ) 1 := by
      refine ⟨by positivity, ?_⟩
      have : y₁ ≤ lam⁻¹ := hy₁.2.trans (min_le_right _ _)
      calc lam * y₁ ≤ lam * lam⁻¹ := mul_le_mul_of_nonneg_left this hlam.le
        _ = 1 := mul_inv_cancel₀ hlam.ne'
    have hDy := hD (lam * y₁) hly
    have hB7 := rescale_expansion e cD lam hlam y₁ hy₁0
    rw [hW y₁ hy₁0]
    have hfac : ∑ i : Fin n, ∑ j : Fin J, κ₀ * cR i j * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)) =
        κ₀ * ∑ i : Fin n, ∑ j : Fin J, cR i j * ((y₁ : ℂ) ^ e i * ((Real.log y₁ : ℝ) : ℂ) ^ (j : ℕ)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [hfac, ← mul_sub, norm_mul, ← hB7]
    have hlamθ : lam ^ (ρ + δ) ≤ LAMθ := by
      rcases le_or_gt 0 (ρ + δ) with hθ | hθ
      · have : lam ^ (ρ + δ) ≤ (lam₀⁻¹) ^ (ρ + δ) := Real.rpow_le_rpow hlam.le hlam_le hθ
        rw [Real.inv_rpow hlam₀.le, ← Real.rpow_neg hlam₀.le] at this
        exact this.trans (le_max_right _ _)
      · exact (Real.rpow_le_rpow_of_nonpos hlam₀ hlam_ge hθ.le).trans (le_max_left _ _)
    calc ‖κ₀‖ * ‖Complex.exp (a' * ((lam * y₁ : ℝ) : ℂ)) * G (lam * y₁) -
          ∑ i : Fin n, ∑ j : Fin J, cD i j * (((lam * y₁ : ℝ) : ℂ) ^ e i * ((Real.log (lam * y₁) : ℝ) : ℂ) ^ (j : ℕ))‖
        ≤ Ω' * (C_D * (lam * y₁) ^ (ρ + δ)) := by
          refine mul_le_mul hκ₀ (hDy.trans (mul_le_mul_of_nonneg_right hCD_mono (by positivity)))
            (norm_nonneg _) hΩ'
      _ = Ω' * C_D * lam ^ (ρ + δ) * y₁ ^ (ρ + δ) := by
          rw [Real.mul_rpow hlam.le hy₁0.le]; ring
      _ ≤ Ω' * C_D * LAMθ * y₁ ^ (ρ + δ) := by
          have hCD0 : 0 ≤ C_D := le_trans (by positivity) hCD_mono
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hlamθ (mul_nonneg hΩ' hCD0))
            (by positivity)

  have hbig : ∀ y₁ ∈ Set.Icc s 1, ‖F y₁‖ ≤ Ω' * W₀ := by
    intro y₁ hy₁
    have hy₁0 : 0 < y₁ := hs0.trans_le hy₁.1
    rw [hW y₁ hy₁0, norm_mul, norm_mul]
    have hexp1 : ‖Complex.exp (a' * ((lam * y₁ : ℝ) : ℂ))‖ = 1 := by
      rw [Complex.norm_exp]
      have : (a' * ((lam * y₁ : ℝ) : ℂ)).re = 0 := by
        rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, ha're]
        ring
      rw [this, Real.exp_zero]
    have hGb : ‖G (lam * y₁)‖ ≤ W₀ := by
      refine hGW (lam * y₁) ?_ ?_
      · calc lam₀ ≤ lam * s := by
              rcases le_or_gt 1 lam⁻¹ with h | h
              · have hs_eq : s = 1 := min_eq_left h
                rw [hs_eq, mul_one]; exact hlam_ge
              · have hs_eq : s = lam⁻¹ := min_eq_right h.le
                rw [hs_eq, mul_inv_cancel₀ hlam.ne']; exact hlam₀1
          _ ≤ lam * y₁ := mul_le_mul_of_nonneg_left hy₁.1 hlam.le
      · calc lam * y₁ ≤ lam * 1 := mul_le_mul_of_nonneg_left hy₁.2 hlam.le
          _ = lam := mul_one lam
          _ ≤ lam₀⁻¹ := hlam_le
    rw [hexp1, one_mul]
    exact mul_le_mul hκ₀ hGb (norm_nonneg _) hΩ'
  intro y₁ hy₁
  simp only [hLc]
  have hext := expansion_extend e (ρ + δ) s hs0 hs1
    F
    (fun i k => κ₀ * cR i k) (Ω' * C_D * LAMθ) (Ω' * W₀) Bfin hvB hsmall hbig y₁ hy₁
  refine hext.trans (mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg hy₁.1.le _))

  have hP_le : ∑ i : Fin n, ∑ j : Fin J, max (s ^ (e i).re) 1 * |Real.log s| ^ (j : ℕ) ≤ P₀ := by
    rw [hP₀]
    refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
    have hlogs : |Real.log s| ≤ |Real.log lam₀| := by
      rw [abs_of_nonpos (Real.log_nonpos hs0.le hs1), abs_of_nonpos (Real.log_nonpos hlam₀.le hlam₀1)]
      linarith [Real.log_le_log hlam₀ hs_lam]
    have hmax : max (s ^ (e i).re) 1 ≤ max (lam₀ ^ (e i).re) 1 := by
      rcases le_or_gt 0 (e i).re with hre' | hre'
      · exact max_le ((Real.rpow_le_one hs0.le hs1 hre').trans (le_max_right _ _)) (le_max_right _ _)
      · exact max_le ((Real.rpow_le_rpow_of_nonpos hlam₀ hs_lam hre'.le).trans (le_max_left _ _)) (le_max_right _ _)
    exact mul_le_mul hmax (pow_le_pow_left₀ (abs_nonneg _) hlogs _) (by positivity) (by positivity)
  have hm_ge : m₀ ≤ min (s ^ (ρ + δ)) 1 := by
    rw [hm₀]
    rcases le_or_gt 0 (ρ + δ) with hθ | hθ
    · exact min_le_min (Real.rpow_le_rpow hlam₀.le hs_lam hθ) le_rfl
    · exact (min_le_right _ _).trans (le_min (Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1 hθ.le) le_rfl)
  have hmin_pos : 0 < min (s ^ (ρ + δ)) 1 := lt_min (Real.rpow_pos_of_pos hs0 _) one_pos
  refine max_le_max le_rfl ?_
  calc (Ω' * W₀ + Bfin * ∑ i : Fin n, ∑ j : Fin J, max (s ^ (e i).re) 1 * |Real.log s| ^ (j : ℕ)) /
        min (s ^ (ρ + δ)) 1
      ≤ (Ω' * W₀ + Bfin * P₀) / min (s ^ (ρ + δ)) 1 := by
        exact div_le_div_of_nonneg_right (add_le_add le_rfl (mul_le_mul_of_nonneg_left hP_le hBfin0))
          hmin_pos.le
    _ ≤ (Ω' * W₀ + Bfin * P₀) / m₀ := by
        have hP0 : 0 ≤ P₀ := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
          mul_nonneg (le_max_of_le_right zero_le_one) (pow_nonneg (abs_nonneg _) _)
        have : 0 ≤ Ω' * W₀ + Bfin * P₀ := add_nonneg (mul_nonneg hΩ' hW₀0) (mul_nonneg hBfin0 hP0)
        exact div_le_div_of_nonneg_left this hm₀pos hm_ge

end S_RegularSingular_exists_transferMatrix_expLogExpansion_rescale_expTwist
end P2MW
export P2MW.S_RegularSingular_exists_transferMatrix_expLogExpansion_rescale_expTwist (solution)
