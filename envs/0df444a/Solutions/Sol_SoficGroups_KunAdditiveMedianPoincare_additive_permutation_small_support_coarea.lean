-- Prove2me | solution 1 for SoficGroups.KunAdditiveMedianPoincare.additive_permutation_small_support_coarea
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.855273+00:00
-- url     : https://prove2.me/submissions/f690eece-f5bf-42a8-ad07-2898d56db9f0

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_sum_indicator_real_eq_mul_card
import Theorems.Thm_SoficGroups_KunAdditiveMedianPoincare_permutationRealVariation_subtract_layer

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunAdditiveMedianPoincare
open SoficGroups.CheegerPoincare
open Filter Topology
open scoped BigOperators
namespace SoficGroups.KunAdditiveMedianPoincare
theorem _root_.solution
    {V ι : Type*} [Fintype V]
    [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (γ ε : ℝ)
    (hε : 0 ≤ ε)
    (hexp : ∀ A : Finset V,
      γ * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ) + ε)
    (f : V → ℝ) (M : ℝ) (hM : 0 ≤ M)
    (hf : ∀ x, 0 ≤ f x)
    (hfM : ∀ x, f x ≤ M)
    (hhalf :
      2 * (SoficGroups.CheegerPoincare.positiveSupport f).card ≤
        Fintype.card V) :
    2 * γ * (∑ x : V, f x) ≤
      permutationRealVariation σ f + 2 * ε * M := by
  classical
  generalize hn :
    (SoficGroups.CheegerPoincare.positiveSupport f).card = n
  induction n using Nat.strong_induction_on generalizing f M with
  | h n ih =>
    by_cases hnonempty :
        (SoficGroups.CheegerPoincare.positiveSupport f).Nonempty
    · let A : Finset V :=
        SoficGroups.CheegerPoincare.positiveSupport f
      have hA : A.Nonempty := hnonempty
      have himage : (A.image f).Nonempty :=
        Finset.image_nonempty.mpr hA
      let m : ℝ := (A.image f).min' himage
      have hmem : m ∈ A.image f := Finset.min'_mem _ _
      obtain ⟨z, hzA, hzm⟩ := Finset.mem_image.mp hmem
      have hmpos : 0 < m := by
        rw [← hzm]
        exact
          (SoficGroups.CheegerPoincare.mem_positiveSupport f z).mp hzA
      have hmle : ∀ x ∈ A, m ≤ f x := by
        intro x hx
        exact Finset.min'_le (A.image f) (f x)
          (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      have hmM : m ≤ M := by
        rw [← hzm]
        exact hfM z
      let g : V → ℝ := fun x =>
        if x ∈ A then f x - m else 0
      have hgnonnegative : ∀ x, 0 ≤ g x := by
        intro x
        by_cases hx : x ∈ A
        · simpa [g, hx] using sub_nonneg.mpr (hmle x hx)
        · simp [g, hx]
      have hgupper : ∀ x, g x ≤ M - m := by
        intro x
        by_cases hx : x ∈ A
        · simp only [g, if_pos hx]
          linarith [hfM x]
        · simp only [g, if_neg hx]
          linarith
      have hgsub :
          SoficGroups.CheegerPoincare.positiveSupport g ⊆ A := by
        intro x hx
        have hpositive :=
          (SoficGroups.CheegerPoincare.mem_positiveSupport g x).mp hx
        by_contra hxA
        simp [g, hxA] at hpositive
      have hznot :
          z ∉ SoficGroups.CheegerPoincare.positiveSupport g := by
        intro hz
        have hpositive :=
          (SoficGroups.CheegerPoincare.mem_positiveSupport g z).mp hz
        have hzero : g z = 0 := by
          simp [g, hzA, hzm]
        simp [hzero] at hpositive
      have hstrict :
          SoficGroups.CheegerPoincare.positiveSupport g ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hgsub, ?_⟩
        intro heq
        exact hznot (heq.symm ▸ hzA)
      have hgcard :
          (SoficGroups.CheegerPoincare.positiveSupport g).card < n := by
        rw [← hn]
        exact Finset.card_lt_card hstrict
      have hghalf :
          2 * (SoficGroups.CheegerPoincare.positiveSupport g).card ≤
            Fintype.card V :=
        (Nat.mul_le_mul_left 2 (Finset.card_le_card hgsub)).trans hhalf
      have hgbound :
          2 * γ * (∑ x : V, g x) ≤
            permutationRealVariation σ g + 2 * ε * (M - m) :=
        ih (SoficGroups.CheegerPoincare.positiveSupport g).card
          hgcard g (M - m) (sub_nonneg.mpr hmM)
          hgnonnegative hgupper hghalf rfl
      have hhalfre : (2 : ℝ) * A.card ≤ Fintype.card V := by
        exact_mod_cast hhalf
      have hmin :
          (A.card : ℝ) ≤ (Fintype.card V : ℝ) - A.card := by
        linarith
      have hcut :
          γ * (A.card : ℝ) ≤
            (SoficGroups.boundary σ A : ℝ) + ε := by
        simpa [min_eq_left hmin] using hexp A
      have houtside : ∀ x, x ∉ A → f x = 0 := by
        intro x hx
        have hnot : ¬ 0 < f x := by
          intro hpositive
          exact hx
            ((SoficGroups.CheegerPoincare.mem_positiveSupport f x).mpr
              hpositive)
        exact le_antisymm (le_of_not_gt hnot) (hf x)
      have hsumindicator :
          (∑ x : V, if x ∈ A then m else 0) =
            m * (A.card : ℝ) := by
        simpa using
          sum_indicator_real_eq_mul_card Finset.univ
            (fun x : V => x ∈ A) m
      have hsum :
          (∑ x : V, f x) =
            (∑ x : V, g x) + m * (A.card : ℝ) := by
        calc
          (∑ x : V, f x) =
              ∑ x : V,
                (g x + if x ∈ A then m else 0) := by
              apply Finset.sum_congr rfl
              intro x _
              by_cases hx : x ∈ A
              · simp [g, hx]
              · simp [g, hx, houtside x hx]
          _ = (∑ x : V, g x) +
              (∑ x : V, if x ∈ A then m else 0) := by
              rw [Finset.sum_add_distrib]
          _ = (∑ x : V, g x) + m * (A.card : ℝ) := by
              rw [hsumindicator]
      have hvariation :
          permutationRealVariation σ f =
            permutationRealVariation σ g +
              2 * m * (SoficGroups.boundary σ A : ℝ) :=
        permutationRealVariation_subtract_layer
          σ f A m hmpos.le hmle houtside
      have hscaled :=
        mul_le_mul_of_nonneg_left hcut
          (show 0 ≤ 2 * m by positivity)
      rw [hsum, hvariation]
      nlinarith
    · have hzero : ∀ x, f x = 0 := by
        intro x
        have hx : ¬ 0 < f x := by
          intro hpositive
          apply hnonempty
          exact ⟨x,
            (SoficGroups.CheegerPoincare.mem_positiveSupport f x).mpr
              hpositive⟩
        exact le_antisymm (le_of_not_gt hx) (hf x)
      simp [permutationRealVariation, hzero]
      positivity
end SoficGroups.KunAdditiveMedianPoincare
