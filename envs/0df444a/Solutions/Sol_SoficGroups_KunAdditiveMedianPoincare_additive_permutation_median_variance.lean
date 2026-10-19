-- Prove2me | solution 1 for SoficGroups.KunAdditiveMedianPoincare.additive_permutation_median_variance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/674226f2-1eb3-401a-9309-8d4076b4d355

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CheegerPoincare_sum_sq_sub_finiteMean_le
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_additive_permutation_median_absolute_deviation

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunAdditiveMedianPoincare
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Nonempty V]
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ε : ℝ)
    (hγ : 0 ≤ γ)
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ) + ε)
    (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) :
    2 * γ *
        (∑ x : V,
          (f x - SoficGroups.CheegerPoincare.finiteMean f) ^ 2) ≤
      permutationRealVariation σ f + 4 * ε := by
  obtain ⟨m, hm_nonnegative, hm_one, hmedian⟩ :=
    additive_permutation_median_absolute_deviation
      σ γ ε hε hexp f hf hf_one
  have hpoint (x : V) : (f x - m) ^ 2 ≤ |f x - m| := by
    have hlower : -1 ≤ f x - m := by
      linarith [hf x]
    have hupper : f x - m ≤ 1 := by
      linarith [hf_one x]
    rcases le_total 0 (f x - m) with hx | hx
    · rw [abs_of_nonneg hx]
      nlinarith
    · rw [abs_of_nonpos hx]
      nlinarith
  have hsq :
      (∑ x : V, (f x - m) ^ 2) ≤
        ∑ x : V, |f x - m| := by
    exact Finset.sum_le_sum fun x _ => hpoint x
  have hmean :=
    SoficGroups.CheegerPoincare.sum_sq_sub_finiteMean_le f m
  have hfactor : 0 ≤ 2 * γ := mul_nonneg (by norm_num) hγ
  calc
    2 * γ *
        (∑ x : V,
          (f x - SoficGroups.CheegerPoincare.finiteMean f) ^ 2) ≤
        2 * γ * (∑ x : V, (f x - m) ^ 2) :=
      mul_le_mul_of_nonneg_left hmean hfactor
    _ ≤ 2 * γ * (∑ x : V, |f x - m|) :=
      mul_le_mul_of_nonneg_left hsq hfactor
    _ ≤ permutationRealVariation σ f + 4 * ε := hmedian
end SoficGroups.KunAdditiveMedianPoincare
