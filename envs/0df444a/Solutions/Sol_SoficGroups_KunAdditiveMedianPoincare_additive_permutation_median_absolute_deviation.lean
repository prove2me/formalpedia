-- Prove2me | solution 1 for SoficGroups.KunAdditiveMedianPoincare.additive_permutation_median_absolute_deviation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/268e01cd-d21a-41cb-bc2e-db7fc5100266

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_CheegerPoincare_positiveSupport_max_sub
import Theorems.Thm_SoficGroups_CheegerPoincare_positiveSupport_max_sub_reverse
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_additive_permutation_small_support_coarea
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_permutationRealVariation_positive_negative
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_exists_bounded_finite_real_median

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
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ) + ε)
    (f : V → ℝ)
    (hf : ∀ x, 0 ≤ f x)
    (hf_one : ∀ x, f x ≤ 1) :
    ∃ m : ℝ, 0 ≤ m ∧ m ≤ 1 ∧
      2 * γ * (∑ x : V, |f x - m|) ≤
        permutationRealVariation σ f + 4 * ε := by
  classical
  obtain ⟨m, hm_nonnegative, hm_one, hbelow, habove⟩ :=
    exists_bounded_finite_real_median f hf hf_one
  let p : V → ℝ := fun x => max (f x - m) 0
  let q : V → ℝ := fun x => max (m - f x) 0
  have hp_nonnegative : ∀ x, 0 ≤ p x := by
    intro x
    exact le_max_right _ _
  have hq_nonnegative : ∀ x, 0 ≤ q x := by
    intro x
    exact le_max_right _ _
  have hp_one : ∀ x, p x ≤ 1 := by
    intro x
    apply max_le
    · linarith [hf_one x]
    · norm_num
  have hq_one : ∀ x, q x ≤ 1 := by
    intro x
    apply max_le
    · linarith [hf x]
    · norm_num
  have hp_half :
      2 * (SoficGroups.CheegerPoincare.positiveSupport p).card ≤
        Fintype.card V := by
    simpa only [p, SoficGroups.CheegerPoincare.positiveSupport_max_sub]
      using habove
  have hq_half :
      2 * (SoficGroups.CheegerPoincare.positiveSupport q).card ≤
        Fintype.card V := by
    simpa only [q,
      SoficGroups.CheegerPoincare.positiveSupport_max_sub_reverse]
      using hbelow
  have hp_coarea := additive_permutation_small_support_coarea
    σ γ ε hε hexp p 1 (by norm_num) hp_nonnegative hp_one hp_half
  have hq_coarea := additive_permutation_small_support_coarea
    σ γ ε hε hexp q 1 (by norm_num) hq_nonnegative hq_one hq_half
  have hvariation :
      permutationRealVariation σ p +
        permutationRealVariation σ q =
          permutationRealVariation σ f := by
    simpa only [p, q] using
      permutationRealVariation_positive_negative σ f m
  have hpoint (x : V) : p x + q x = |f x - m| := by
    dsimp [p, q]
    rcases le_total m (f x) with hx | hx
    · rw [max_eq_left (sub_nonneg.mpr hx),
        max_eq_right (sub_nonpos.mpr hx),
        abs_of_nonneg (sub_nonneg.mpr hx)]
      ring
    · rw [max_eq_right (sub_nonpos.mpr hx),
        max_eq_left (sub_nonneg.mpr hx),
        abs_of_nonpos (sub_nonpos.mpr hx)]
      ring
  have hmass :
      (∑ x : V, p x) + (∑ x : V, q x) =
        ∑ x : V, |f x - m| := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    exact hpoint x
  refine ⟨m, hm_nonnegative, hm_one, ?_⟩
  rw [← hmass, ← hvariation]
  nlinarith [hp_coarea, hq_coarea]
end SoficGroups.KunAdditiveMedianPoincare
