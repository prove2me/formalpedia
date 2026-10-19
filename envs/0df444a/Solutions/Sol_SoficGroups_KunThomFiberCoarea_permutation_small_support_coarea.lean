-- Prove2me | solution 1 for SoficGroups.KunThomFiberCoarea.permutation_small_support_coarea
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.294654+00:00
-- url     : https://prove2.me/submissions/40b26cc0-9018-4b5b-826d-3d21a9468cef

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_sum_indicator_nat_eq_mul_card
import Theorems.Thm_SoficGroups_KunThomFiberCoarea_permutationVariation_subtract_layer

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomFiberCoarea
namespace SoficGroups.KunThomFiberCoarea
theorem _root_.solution
    {V ι : Type*} [Fintype V] [Fintype ι] [DecidableEq V]
    (σ : ι → Equiv.Perm V) (h : ℝ)
    (hexp : ∀ A : Finset V,
      h * min (A.card : ℝ)
        ((Fintype.card V : ℝ) - A.card) ≤
          (SoficGroups.boundary σ A : ℝ))
    (f : V → ℕ)
    (hhalf : 2 * (positiveNatSupport f).card ≤ Fintype.card V) :
    2 * h * (∑ x : V, f x) ≤
      (permutationVariation σ f : ℝ) := by
  classical
  generalize hn : (positiveNatSupport f).card = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hnonempty : (positiveNatSupport f).Nonempty
    · let A : Finset V := positiveNatSupport f
      have hA : A.Nonempty := hnonempty
      have himage : (A.image f).Nonempty := Finset.image_nonempty.mpr hA
      let m : ℕ := (A.image f).min' himage
      have hm_mem : m ∈ A.image f := Finset.min'_mem _ _
      obtain ⟨z, hzA, hzm⟩ := Finset.mem_image.mp hm_mem
      have hmpos : 0 < m := by
        rw [← hzm]
        exact (mem_positiveNatSupport f z).mp hzA
      have hm_le : ∀ x ∈ A, m ≤ f x := by
        intro x hx
        exact Finset.min'_le (A.image f) (f x)
          (Finset.mem_image.mpr ⟨x, hx, rfl⟩)
      let g : V → ℕ := fun x => if x ∈ A then f x - m else 0
      have hg_sub : positiveNatSupport g ⊆ A := by
        intro x hx
        have hxpos := (mem_positiveNatSupport g x).mp hx
        by_contra hxA
        simp [g, hxA] at hxpos
      have hz_not : z ∉ positiveNatSupport g := by
        intro hz
        have hzpos := (mem_positiveNatSupport g z).mp hz
        have hzero : g z = 0 := by
          simp [g, hzA, hzm]
        simp [hzero] at hzpos
      have hstrict : positiveNatSupport g ⊂ A := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hg_sub, ?_⟩
        intro heq
        exact hz_not (heq.symm ▸ hzA)
      have hg_card : (positiveNatSupport g).card < n := by
        rw [← hn]
        exact Finset.card_lt_card hstrict
      have hg_half :
          2 * (positiveNatSupport g).card ≤ Fintype.card V :=
        (Nat.mul_le_mul_left 2 (Finset.card_le_card hg_sub)).trans hhalf
      have hg_bound :
          2 * h * (∑ x : V, g x) ≤
            (permutationVariation σ g : ℝ) :=
        ih (positiveNatSupport g).card hg_card g hg_half rfl
      have hg_bound' :
          2 * h * (∑ x : V, (g x : ℝ)) ≤
            (permutationVariation σ g : ℝ) := by
        simpa only [Nat.cast_sum] using hg_bound
      have hhalf_real :
          (2 : ℝ) * A.card ≤ Fintype.card V := by
        exact_mod_cast hhalf
      have hmin :
          (A.card : ℝ) ≤ (Fintype.card V : ℝ) - A.card := by
        linarith
      have hcut :
          h * (A.card : ℝ) ≤
            (SoficGroups.boundary σ A : ℝ) := by
        simpa [min_eq_left hmin] using hexp A
      have houtside : ∀ x, x ∉ A → f x = 0 := by
        intro x hx
        have hxnot : ¬ 0 < f x := by
          intro hpos
          exact hx ((mem_positiveNatSupport f x).mpr hpos)
        omega
      have hsum :
          (∑ x : V, f x) =
            (∑ x : V, g x) + m * A.card := by
        calc
          (∑ x : V, f x) =
              ∑ x : V, (g x + if x ∈ A then m else 0) := by
                apply Finset.sum_congr rfl
                intro x _
                by_cases hx : x ∈ A
                · have hxlow := hm_le x hx
                  simp [g, hx]
                  omega
                · simp [g, hx, houtside x hx]
          _ = (∑ x : V, g x) +
                (∑ x : V, if x ∈ A then m else 0) := by
                rw [Finset.sum_add_distrib]
          _ = (∑ x : V, g x) + m * A.card := by
                rw [sum_indicator_nat_eq_mul_card]
                simp
      have hvar :
          permutationVariation σ f =
            permutationVariation σ g +
              2 * m * SoficGroups.boundary σ A :=
        permutationVariation_subtract_layer
          σ f A m hm_le houtside
      calc
        2 * h * (∑ x : V, f x) =
            2 * h *
              ((∑ x : V, (g x : ℝ)) +
                (m : ℝ) * (A.card : ℝ)) := by
              rw [hsum]
              simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_sum]
        _ = 2 * h * (∑ x : V, (g x : ℝ)) +
              (2 * (m : ℝ)) * (h * (A.card : ℝ)) := by
              ring
        _ ≤ (permutationVariation σ g : ℝ) +
              (2 * (m : ℝ)) *
                (SoficGroups.boundary σ A : ℝ) := by
              apply add_le_add hg_bound'
              exact mul_le_mul_of_nonneg_left hcut (by positivity)
        _ = (permutationVariation σ f : ℝ) := by
              exact_mod_cast hvar.symm
    · have hzero : ∀ x, f x = 0 := by
        intro x
        by_contra hx
        apply hnonempty
        refine ⟨x, (mem_positiveNatSupport f x).mpr ?_⟩
        exact Nat.pos_of_ne_zero hx
      simp [permutationVariation, hzero]
end SoficGroups.KunThomFiberCoarea
