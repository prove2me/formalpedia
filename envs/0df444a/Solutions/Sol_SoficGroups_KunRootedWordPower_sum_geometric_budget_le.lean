-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.sum_geometric_budget_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/342b6207-75a9-471a-8f40-7d5562098d17

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    (q : ℝ) (hqzero : 0 ≤ q) (hqone : q < 1) (k : ℕ) :
    (∑ j ∈ Finset.range k,
      (q ^ j +
        (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹)) ≤
      2 / (1 - q) := by
  have hgap : 0 < 1 - q := sub_pos.mpr hqone
  have hkpos : 0 < ((k + 1 : ℕ) : ℝ) := by positivity
  have hgeom :
      (∑ j ∈ Finset.range k, q ^ j) ≤ (1 - q)⁻¹ := by
    simpa using
      (geom_sum_Ico_le_of_lt_one (m := 0) (n := k)
        hqzero hqone)
  have hratio :
      (k : ℝ) / ((k + 1 : ℕ) : ℝ) ≤ 1 := by
    apply (div_le_iff₀ hkpos).2
    rw [one_mul]
    exact_mod_cast Nat.le_succ k
  have hnoise :
      (k : ℝ) *
        (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹ ≤
        (1 - q)⁻¹ := by
    calc
      (k : ℝ) *
          (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹ =
        ((k : ℝ) / ((k + 1 : ℕ) : ℝ)) *
          (1 - q)⁻¹ := by
            field_simp
      _ ≤ 1 * (1 - q)⁻¹ :=
        mul_le_mul_of_nonneg_right hratio
          (inv_nonneg.mpr hgap.le)
      _ = (1 - q)⁻¹ := one_mul _
  calc
    (∑ j ∈ Finset.range k,
      (q ^ j + (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹)) =
        (∑ j ∈ Finset.range k, q ^ j) +
          (k : ℝ) *
            (((k + 1 : ℕ) : ℝ) * (1 - q))⁻¹ := by
              rw [Finset.sum_add_distrib]
              simp
    _ ≤ (1 - q)⁻¹ + (1 - q)⁻¹ :=
      add_le_add hgeom hnoise
    _ = 2 / (1 - q) := by ring
end SoficGroups.KunRootedWordPower
