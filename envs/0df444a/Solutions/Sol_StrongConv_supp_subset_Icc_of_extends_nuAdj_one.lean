-- Prove2me | solution 1 for StrongConv.supp_subset_Icc_of_extends_nuAdj_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-04T23:30:42.332888+00:00
-- url     : https://prove2.me/submissions/efceec8b-f981-4532-ba1c-4d21ff6b88e8

import Mathlib
import Definitions.Def_StrongConv
import Theorems.Thm_StrongConv_nuAdj_one_pow_eq
import Theorems.Thm_StrongConv_card_wordFree_eq_pow_le
import Theorems.Thm_StrongConv_supp_subset_Icc_limsup

open Polynomial Filter Topology

namespace StrongConv

lemma C84_norm_delta (d : ℕ) : ‖delta (d := d) 1‖ = 1 := by
  simp [delta]

lemma C84_abs_tau_pow_le (d p : ℕ) (hp : 1 ≤ p) :
    |(tau (adjFree d ^ p)).re| ≤ ‖adjFree d‖ ^ p := by
  have h1 : ‖(adjFree d ^ p) (delta (d := d) 1)‖ ≤ ‖adjFree d‖ ^ p := by
    have := (adjFree d ^ p).le_opNorm (delta (d := d) 1)
    rw [C84_norm_delta, mul_one] at this
    exact this.trans (norm_pow_le' _ (by omega))
  calc |(tau (adjFree d ^ p)).re| ≤ ‖tau (adjFree d ^ p)‖ := Complex.abs_re_le_norm _
    _ ≤ ‖delta (d := d) 1‖ * ‖(adjFree d ^ p) (delta 1)‖ := by
        unfold tau; exact norm_inner_le_norm _ _
    _ ≤ ‖adjFree d‖ ^ p := by rw [C84_norm_delta, one_mul]; exact h1

lemma C84_moment_bound (d p : ℕ) (hp : 1 ≤ p) :
    |nuAdj d 1 (X ^ p)| ≤ (1 + (p : ℝ) ^ 2 * ((p : ℝ) + 1) ^ 4) * ‖adjFree d‖ ^ p := by
  rw [nuAdj_one_pow_eq d p hp]
  set R := ‖adjFree d‖ with hR
  have hR0 : 0 ≤ R := norm_nonneg _
  have h1 := C84_abs_tau_pow_le d p hp
  have h2 : ∀ k ∈ Finset.Icc 2 p, |((k.divisors.card : ℝ) - 1) *
        (Nat.card {x : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
          IsNonPower x.2 ∧ wordFree (List.ofFn fun j => some (x.1 j)) = x.2 ^ k} : ℝ)| ≤
        (p : ℝ) * (((p : ℝ) + 1) ^ 4 * R ^ p) := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hcard := card_wordFree_eq_pow_le d k p hk.1 hp
    have hω : (k.divisors.card : ℝ) ≤ p := by
      exact_mod_cast (Nat.card_divisors_le_self k).trans hk.2
    have hω1 : (1 : ℝ) ≤ k.divisors.card := by
      exact_mod_cast Finset.card_pos.mpr ⟨1, by simp; omega⟩
    rw [abs_mul, abs_of_nonneg (by linarith : (0:ℝ) ≤ k.divisors.card - 1),
      abs_of_nonneg (Nat.cast_nonneg _)]
    exact mul_le_mul (by linarith) hcard (Nat.cast_nonneg _) (by positivity)
  have h3 : |∑ k ∈ Finset.Icc 2 p, ((k.divisors.card : ℝ) - 1) *
        (Nat.card {x : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
          IsNonPower x.2 ∧ wordFree (List.ofFn fun j => some (x.1 j)) = x.2 ^ k} : ℝ)| ≤
        p * ((p : ℝ) * (((p : ℝ) + 1) ^ 4 * R ^ p)) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum h2).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have : ((Finset.Icc 2 p).card : ℝ) ≤ p := by
      rw [Nat.card_Icc]; exact_mod_cast (by omega : p + 1 - 2 ≤ p)
    exact mul_le_mul_of_nonneg_right this (by positivity)
  have h4 := abs_add_le (-(tau (adjFree d ^ p)).re) (∑ k ∈ Finset.Icc 2 p, ((k.divisors.card : ℝ) - 1) *
        (Nat.card {x : (Fin p → Fin d ⊕ Fin d) × FreeGroup (Fin d) //
          IsNonPower x.2 ∧ wordFree (List.ofFn fun j => some (x.1 j)) = x.2 ^ k} : ℝ))
  rw [abs_neg] at h4
  nlinarith [h1, h3, h4]


lemma C84_const_bound (p : ℕ) (hp : 1 ≤ p) :
    1 + (p : ℝ) ^ 2 * ((p : ℝ) + 1) ^ 4 ≤ (((p : ℝ) + 1) ^ (7 : ℕ)) := by
  have h1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have : (p : ℝ) ^ 2 ≤ ((p : ℝ) + 1) ^ 2 := by nlinarith
  have h2 : (1 : ℝ) ≤ ((p : ℝ) + 1) ^ 6 := one_le_pow₀ (by linarith)
  have h3 : ((p : ℝ) + 1) ^ 6 ≤ ((p : ℝ) + 1) ^ 6 * (p : ℝ) := by nlinarith
  calc 1 + (p : ℝ) ^ 2 * ((p : ℝ) + 1) ^ 4 ≤ 1 + ((p : ℝ) + 1) ^ 2 * ((p : ℝ) + 1) ^ 4 := by gcongr
    _ = 1 + ((p : ℝ) + 1) ^ 6 := by ring
    _ ≤ ((p : ℝ) + 1) ^ 6 + ((p : ℝ) + 1) ^ 6 * (p : ℝ) := by linarith
    _ = ((p : ℝ) + 1) ^ 7 := by ring

lemma C84_tendsto_root :
    Tendsto (fun p : ℕ => (((p : ℝ) + 1) ^ (7 : ℕ)) ^ (1 / (p : ℝ))) atTop (𝓝 1) := by
  have h := (tendsto_rpow_div_mul_add (7 : ℝ) 1 (-1) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop.atTop_add (tendsto_const_nhds (x := (1 : ℝ))))
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with p hp
  simp only [Function.comp]
  have hp0 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
  rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
  congr 1
  have : (1 : ℝ) * ((p : ℝ) + 1) + -1 = p := by ring
  rw [this]
  ring

lemma C84_limsup_le (d : ℕ) :
    limsup (fun p : ℕ => |nuAdj d 1 (X ^ p)| ^ (1 / (p : ℝ))) atTop ≤ ‖adjFree d‖ := by
  set R := ‖adjFree d‖ with hR
  have hR0 : 0 ≤ R := norm_nonneg _
  have key : ∀ᶠ p : ℕ in atTop, |nuAdj d 1 (X ^ p)| ^ (1 / (p : ℝ)) ≤
      (((p : ℝ) + 1) ^ (7 : ℕ)) ^ (1 / (p : ℝ)) * R := by
    filter_upwards [eventually_ge_atTop 1] with p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
    have hb := (C84_moment_bound d p hp).trans (mul_le_mul_of_nonneg_right
      (C84_const_bound p hp) (pow_nonneg hR0 _))
    calc |nuAdj d 1 (X ^ p)| ^ (1 / (p : ℝ))
        ≤ ((((p : ℝ) + 1) ^ (7 : ℕ)) * R ^ p) ^ (1 / (p : ℝ)) :=
          Real.rpow_le_rpow (abs_nonneg _) hb (by positivity)
      _ = (((p : ℝ) + 1) ^ (7 : ℕ)) ^ (1 / (p : ℝ)) * (R ^ p) ^ (1 / (p : ℝ)) :=
          Real.mul_rpow (by positivity) (pow_nonneg hR0 _)
      _ = _ := by
          congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_mul hR0]
          rw [mul_one_div_cancel hp0.ne', Real.rpow_one]
  have hlim : Tendsto (fun p : ℕ => (((p : ℝ) + 1) ^ (7 : ℕ)) ^ (1 / (p : ℝ)) * R) atTop (𝓝 R) := by
    simpa using C84_tendsto_root.mul_const R
  refine (limsup_le_limsup key ?_ ?_).trans hlim.limsup_eq.le
  · exact isCoboundedUnder_le_of_le atTop (x := 0) (fun p => by positivity)
  · exact hlim.isBoundedUnder_le

theorem supp_subset_Icc_of_extends_nuAdj_one_dev (d : ℕ) (μ : smoothFun →ₗ[ℝ] ℝ)
    (hμ : IsCSDistribution μ) (hext : ∀ h : ℝ[X], μ (polyFun h) = nuAdj d 1 h) :
    supp μ ⊆ Set.Icc (-‖adjFree d‖) ‖adjFree d‖ := by
  refine (supp_subset_Icc_limsup μ hμ).trans (Set.Icc_subset_Icc ?_ ?_)
  · have := C84_limsup_le d
    simp only [hext] at this ⊢
    linarith
  · have := C84_limsup_le d
    simpa only [hext] using this

end StrongConv

theorem solution : type_of% @StrongConv.supp_subset_Icc_of_extends_nuAdj_one_dev :=
  @StrongConv.supp_subset_Icc_of_extends_nuAdj_one_dev
