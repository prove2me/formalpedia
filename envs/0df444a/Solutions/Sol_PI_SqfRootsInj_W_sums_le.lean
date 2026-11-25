-- Prove2me | solution 1 for PI.SqfRootsInj.W.sums_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:55:13.871313+00:00
-- url     : https://prove2.me/submissions/771996fa-13e2-44bb-adbb-9e3dc884d726

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_SumSqPowLeTwo
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SquarefreeRootsInjective_RpowQuarterPowFour
import Theorems.Thm_PI_SqfRootsInj_W_rpow_quarter_pow_four
import Theorems.Thm_PI_SqfRootsInj_W_rpow_neg_half_eq
import Theorems.Thm_PI_SqfRootsInj_W_termA_le
import Theorems.Thm_PI_SqfRootsInj_W_termB_le
import Theorems.Thm_PI_SqfRootsInj_W_log_cast_le
import Theorems.Thm_PI_SqfRootsInj_W_card_LS_le
import Theorems.Thm_PI_SqfRootsInj_W_g_pow_sub_one_ne
import Theorems.Thm_PI_SqfRootsInj_W_sum_sq_pow_le_one
import Theorems.Thm_PI_SqfRootsInj_W_sum_sq_pow_le_two


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
noncomputable section
open Classical
open PI PI.SqfRootsInj PI.SqfRootsInj.W
open PI.SqfLab
namespace PI.SqfRootsInj.W
theorem _root_.solution (g r : ℕ) [hgp : Fact g.Prime] (hg : 2 ^ 12 ≤ g) :
    ((SA g r + SB g r : ℕ) : ℝ) ≤ 23 * Real.log g * (g : ℝ) ^ (-(1 / 2 : ℝ)) * (g : ℝ) ^ r := by
  have hg1 : 1 < g := hgp.out.one_lt
  have hg0 : (0 : ℝ) ≤ g := Nat.cast_nonneg g
  set s := (g : ℝ) ^ ((1 : ℝ) / 4) with hs
  have hs4 : s ^ 4 = g := rpow_quarter_pow_four _ hg0
  have hsn : 0 ≤ s := Real.rpow_nonneg hg0 _
  have hs8 : 8 ≤ s := by
    by_contra h
    push Not at h
    have h1 : s ^ 4 < 8 ^ 4 := pow_lt_pow_left₀ h hsn (by norm_num)
    rw [hs4] at h1
    have h2 : ((2 ^ 12 : ℕ) : ℝ) ≤ g := by exact_mod_cast hg
    norm_num at h1 h2
    linarith
  have hs0 : 0 < s := by linarith
  have hs1 : 1 ≤ s := by linarith
  set t := s⁻¹ with ht
  have ht0 : 0 ≤ t := inv_nonneg.2 hsn
  have ht8 : t ≤ 1 / 8 := by
    rw [ht, one_div]; exact inv_anti₀ (by norm_num) hs8
  have hl2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hl2p : 0 < Real.log 2 := by linarith
  have hA : 0 ≤ Real.log g := Real.log_nonneg (by exact_mod_cast hg1.le)
  set large₂ := Real.log g / Real.log 2 with hLg
  have hLg0 : 0 ≤ large₂ := div_nonneg hA hl2p.le
  have hLg2 : large₂ ≤ 2 * Real.log g := by
    rw [hLg, div_le_iff₀ hl2p]; nlinarith
  have hG : (0 : ℝ) ≤ (g : ℝ) ^ r := by positivity
  have hne : ∀ e, 1 ≤ e → g ^ e - 1 ≠ 0 := fun e he => g_pow_sub_one_ne hg1 he

  have hSA : (SA g r : ℝ) ≤ 4 * large₂ * (g : ℝ) ^ r * t ^ 2 := by
    have hper : ∀ e ∈ Finset.Icc 2 r,
        (∑ j ∈ Finset.Icc 1 (e / 2), ∑ ℓ ∈ LS g r (g ^ e - 1),
          (((g ^ j - 1) * Lp g e ℓ * g ^ (r - e) : ℕ) : ℝ)) ≤
          (large₂ * (g : ℝ) ^ r / 2) * ((e : ℝ) ^ 2 * t ^ e) := by
      intro e he
      obtain ⟨he2, her⟩ := Finset.mem_Icc.1 he
      have hcj : ((Finset.Icc 1 (e / 2)).card : ℝ) ≤ (e : ℝ) / 2 := by
        have h1 : (Finset.Icc 1 (e / 2)).card = e / 2 := by simp
        rw [h1]
        have := (Nat.cast_div_le (m := e) (n := 2) : ((e / 2 : ℕ) : ℝ) ≤ _)
        simpa using this
      have hcl : ((LS g r (g ^ e - 1)).card : ℝ) ≤ e * large₂ := by
        refine (card_LS_le g r _ (hne e (by omega))).trans ?_
        rw [hLg, mul_div_assoc']
        exact div_le_div_of_nonneg_right (log_cast_le _ g e (hne e (by omega)) (Nat.sub_le _ _))
          hl2p.le
      calc (∑ j ∈ Finset.Icc 1 (e / 2), ∑ ℓ ∈ LS g r (g ^ e - 1),
            (((g ^ j - 1) * Lp g e ℓ * g ^ (r - e) : ℕ) : ℝ))
          ≤ ∑ j ∈ Finset.Icc 1 (e / 2), ∑ ℓ ∈ LS g r (g ^ e - 1), (g : ℝ) ^ r * t ^ e := by
            refine Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun ℓ hℓ => ?_
            have hj' := Finset.mem_Icc.1 hj
            obtain ⟨hℓ1, hℓB⟩ := Finset.mem_filter.1 hℓ
            exact termA_le g r e j ℓ s hs0 hs1 hs4 (Nat.prime_of_mem_primeFactors hℓ1) hℓB
              (by omega) her (by omega)
        _ = ((Finset.Icc 1 (e / 2)).card : ℝ) *
              (((LS g r (g ^ e - 1)).card : ℝ) * ((g : ℝ) ^ r * t ^ e)) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ((e : ℝ) / 2) * ((e * large₂) * ((g : ℝ) ^ r * t ^ e)) := by
            apply mul_le_mul hcj (mul_le_mul_of_nonneg_right hcl (by positivity))
              (by positivity) (by positivity)
        _ = (large₂ * (g : ℝ) ^ r / 2) * ((e : ℝ) ^ 2 * t ^ e) := by ring
    calc (SA g r : ℝ) = ∑ e ∈ Finset.Icc 2 r, ∑ j ∈ Finset.Icc 1 (e / 2),
          ∑ ℓ ∈ LS g r (g ^ e - 1), (((g ^ j - 1) * Lp g e ℓ * g ^ (r - e) : ℕ) : ℝ) := by
          simp only [SA, Nat.cast_sum]
      _ ≤ ∑ e ∈ Finset.Icc 2 r, (large₂ * (g : ℝ) ^ r / 2) * ((e : ℝ) ^ 2 * t ^ e) :=
          Finset.sum_le_sum hper
      _ = (large₂ * (g : ℝ) ^ r / 2) * ∑ e ∈ Finset.Icc 2 r, (e : ℝ) ^ 2 * t ^ e := by
          rw [Finset.mul_sum]
      _ ≤ (large₂ * (g : ℝ) ^ r / 2) * (8 * t ^ 2) := by
          gcongr
          exact sum_sq_pow_le_two t ht0 ht8 r
      _ = 4 * large₂ * (g : ℝ) ^ r * t ^ 2 := by ring

  have hSB : (SB g r : ℝ) ≤ 4 * large₂ * (g : ℝ) ^ r * t ^ 3 := by
    have hper : ∀ e ∈ Finset.Icc 1 r,
        (∑ e' ∈ Finset.Icc 1 (min e (r - e)), ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)),
          ((g ^ e' * Lp g e ℓ * g ^ (r - e - e') : ℕ) : ℝ)) ≤
          (2 * large₂ * (g : ℝ) ^ r) * ((e : ℝ) ^ 2 * t ^ e * t ^ 2) := by
      intro e he
      obtain ⟨he1, her⟩ := Finset.mem_Icc.1 he
      have hce : ((Finset.Icc 1 (min e (r - e))).card : ℝ) ≤ e := by
        have h1 : (Finset.Icc 1 (min e (r - e))).card ≤ e := by simp
        exact_mod_cast h1
      have ht3 : t ^ (3 * e) ≤ t ^ e * t ^ 2 := by
        rw [show 3 * e = e + 2 * e by ring, pow_add]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one ht0 (by linarith) (by omega : 2 ≤ 2 * e)) (pow_nonneg ht0 e)
      calc (∑ e' ∈ Finset.Icc 1 (min e (r - e)), ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)),
            ((g ^ e' * Lp g e ℓ * g ^ (r - e - e') : ℕ) : ℝ))
          ≤ ∑ e' ∈ Finset.Icc 1 (min e (r - e)), ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)),
              (g : ℝ) ^ r * t ^ (3 * e) := by
            refine Finset.sum_le_sum fun e' he' => Finset.sum_le_sum fun ℓ hℓ => ?_
            have he'' := Finset.mem_Icc.1 he'
            obtain ⟨hℓ1, hℓB⟩ := Finset.mem_filter.1 hℓ
            exact termB_le g r e e' ℓ s hs0 hs4 (Nat.prime_of_mem_primeFactors hℓ1) hℓB he1
              (by omega)
        _ = ∑ e' ∈ Finset.Icc 1 (min e (r - e)),
              ((LS g r ((g ^ e - 1) * (g ^ e' - 1))).card : ℝ) * ((g : ℝ) ^ r * t ^ (3 * e)) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ ∑ e' ∈ Finset.Icc 1 (min e (r - e)), (2 * e * large₂) * ((g : ℝ) ^ r * t ^ (3 * e)) := by
            refine Finset.sum_le_sum fun e' he' => ?_
            have he'' := Finset.mem_Icc.1 he'
            have hn0 : (g ^ e - 1) * (g ^ e' - 1) ≠ 0 :=
              Nat.mul_ne_zero (hne e he1) (hne e' he''.1)
            have hnle : (g ^ e - 1) * (g ^ e' - 1) ≤ g ^ (2 * e) := by
              calc (g ^ e - 1) * (g ^ e' - 1) ≤ g ^ e * g ^ e :=
                    Nat.mul_le_mul (Nat.sub_le _ _) ((Nat.sub_le _ _).trans
                      (Nat.pow_le_pow_right (by omega) (by omega)))
                _ = g ^ (2 * e) := by rw [← pow_add, two_mul]
            have hcl : ((LS g r ((g ^ e - 1) * (g ^ e' - 1))).card : ℝ) ≤ 2 * e * large₂ := by
              refine (card_LS_le g r _ hn0).trans ?_
              have := log_cast_le _ g (2 * e) hn0 hnle
              rw [hLg, mul_div_assoc']
              refine div_le_div_of_nonneg_right ?_ hl2p.le
              push_cast at this ⊢
              linarith
            exact mul_le_mul_of_nonneg_right hcl (by positivity)
        _ = ((Finset.Icc 1 (min e (r - e))).card : ℝ) *
              ((2 * e * large₂) * ((g : ℝ) ^ r * t ^ (3 * e))) := by
            simp only [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (e : ℝ) * ((2 * e * large₂) * ((g : ℝ) ^ r * (t ^ e * t ^ 2))) := by
            apply mul_le_mul hce _ (by positivity) (by positivity)
            gcongr
        _ = (2 * large₂ * (g : ℝ) ^ r) * ((e : ℝ) ^ 2 * t ^ e * t ^ 2) := by ring
    calc (SB g r : ℝ) = ∑ e ∈ Finset.Icc 1 r, ∑ e' ∈ Finset.Icc 1 (min e (r - e)),
          ∑ ℓ ∈ LS g r ((g ^ e - 1) * (g ^ e' - 1)),
            ((g ^ e' * Lp g e ℓ * g ^ (r - e - e') : ℕ) : ℝ) := by
          simp only [SB, Nat.cast_sum]
      _ ≤ ∑ e ∈ Finset.Icc 1 r, (2 * large₂ * (g : ℝ) ^ r) * ((e : ℝ) ^ 2 * t ^ e * t ^ 2) :=
          Finset.sum_le_sum hper
      _ = (2 * large₂ * (g : ℝ) ^ r * t ^ 2) * ∑ e ∈ Finset.Icc 1 r, (e : ℝ) ^ 2 * t ^ e := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun e _ => by ring
      _ ≤ (2 * large₂ * (g : ℝ) ^ r * t ^ 2) * (2 * t) := by
          gcongr
          exact sum_sq_pow_le_one t ht0 ht8 r
      _ = 4 * large₂ * (g : ℝ) ^ r * t ^ 3 := by ring
  have ht3 : t ^ 3 ≤ t ^ 2 / 8 := by
    rw [pow_succ]
    have := mul_le_mul_of_nonneg_left ht8 (sq_nonneg t)
    linarith
  rw [rpow_neg_half_eq _ hg0, ← hs, ← ht, Nat.cast_add]
  have hX : 0 ≤ Real.log g * ((g : ℝ) ^ r * t ^ 2) := by positivity
  calc (SA g r : ℝ) + SB g r ≤ 4 * large₂ * (g : ℝ) ^ r * t ^ 2 + 4 * large₂ * (g : ℝ) ^ r * t ^ 3 :=
        add_le_add hSA hSB
    _ ≤ 4 * large₂ * (g : ℝ) ^ r * t ^ 2 + 4 * large₂ * (g : ℝ) ^ r * (t ^ 2 / 8) := by gcongr
    _ = (9 / 2) * large₂ * ((g : ℝ) ^ r * t ^ 2) := by ring
    _ ≤ (9 / 2) * (2 * Real.log g) * ((g : ℝ) ^ r * t ^ 2) := by gcongr
    _ ≤ 23 * Real.log g * t ^ 2 * (g : ℝ) ^ r := by nlinarith
end PI.SqfRootsInj.W
