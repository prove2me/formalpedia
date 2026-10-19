-- Prove2me | solution 1 for SoficGroups.CheegerPoincare.exists_finite_real_median
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/0cd40f34-7e0d-4b80-b476-cb65da135901

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.CheegerPoincare
open scoped BigOperators
namespace SoficGroups.CheegerPoincare
theorem _root_.solution {V : Type*} [Fintype V] [Nonempty V]
    (f : V → ℝ) :
    ∃ m : ℝ,
      2 * (lowerLevel f m).card ≤ Fintype.card V ∧
      2 * (upperLevel f m).card ≤ Fintype.card V := by
  classical
  let values : Finset ℝ := Finset.univ.image f
  have hvalues : values.Nonempty := by
    obtain ⟨x⟩ := ‹Nonempty V›
    refine ⟨f x, ?_⟩
    exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
  let a : ℝ := values.min' hvalues
  have ha_values : a ∈ values := Finset.min'_mem values hvalues
  have ha_lower : lowerLevel f a = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro x hx
    have hx_lt : f x < a := (mem_lowerLevel f a x).mp hx
    have hx_values : f x ∈ values :=
      Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
    exact (not_lt_of_ge (Finset.min'_le values (f x) hx_values)) hx_lt
  let candidates : Finset ℝ :=
    values.filter fun c => 2 * (lowerLevel f c).card ≤ Fintype.card V
  have hcandidates : candidates.Nonempty := by
    refine ⟨a, ?_⟩
    apply Finset.mem_filter.mpr
    refine ⟨ha_values, ?_⟩
    simp [ha_lower]
  let m : ℝ := candidates.max' hcandidates
  have hm_candidates : m ∈ candidates :=
    Finset.max'_mem candidates hcandidates
  have hm_lower : 2 * (lowerLevel f m).card ≤ Fintype.card V :=
    (Finset.mem_filter.mp hm_candidates).2
  refine ⟨m, hm_lower, ?_⟩
  by_contra hu
  have hu_large : Fintype.card V < 2 * (upperLevel f m).card :=
    Nat.lt_of_not_ge hu
  have hu_nonempty : (upperLevel f m).Nonempty := by
    apply Finset.card_pos.mp
    omega
  let upperValues : Finset ℝ := (upperLevel f m).image f
  have hupperValues : upperValues.Nonempty :=
    Finset.image_nonempty.mpr hu_nonempty
  let b : ℝ := upperValues.min' hupperValues
  have hb_upperValues : b ∈ upperValues :=
    Finset.min'_mem upperValues hupperValues
  obtain ⟨z, hz_upper, hz_b⟩ := Finset.mem_image.mp hb_upperValues
  have hmb : m < b := by
    rw [← hz_b]
    exact (mem_upperLevel f m z).mp hz_upper
  have hdisjoint : Disjoint (lowerLevel f b) (upperLevel f m) := by
    apply Finset.disjoint_left.mpr
    intro x hx_lower hx_upper
    have hx_lt : f x < b := (mem_lowerLevel f b x).mp hx_lower
    have hx_image : f x ∈ upperValues :=
      Finset.mem_image.mpr ⟨x, hx_upper, rfl⟩
    have hb_le : b ≤ f x :=
      Finset.min'_le upperValues (f x) hx_image
    exact (not_lt_of_ge hb_le) hx_lt
  have hcard :
      (lowerLevel f b).card + (upperLevel f m).card ≤ Fintype.card V := by
    calc
      (lowerLevel f b).card + (upperLevel f m).card =
          ((lowerLevel f b) ∪ (upperLevel f m)).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ ≤ (Finset.univ : Finset V).card :=
        Finset.card_le_card (Finset.subset_univ _)
      _ = Fintype.card V := Finset.card_univ
  have hb_lower : 2 * (lowerLevel f b).card ≤ Fintype.card V := by
    omega
  have hb_values : b ∈ values := by
    rw [← hz_b]
    exact Finset.mem_image.mpr ⟨z, Finset.mem_univ z, rfl⟩
  have hb_candidates : b ∈ candidates :=
    Finset.mem_filter.mpr ⟨hb_values, hb_lower⟩
  have hb_le_m : b ≤ m :=
    Finset.le_max' candidates b hb_candidates
  exact (not_le_of_gt hmb) hb_le_m
end SoficGroups.CheegerPoincare
