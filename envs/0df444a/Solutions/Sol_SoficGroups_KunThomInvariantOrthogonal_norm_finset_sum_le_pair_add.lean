-- Prove2me | solution 1 for SoficGroups.KunThomInvariantOrthogonal.norm_finset_sum_le_pair_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/21b38a4c-e492-45ff-b43e-c4aa3102b516

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunThomInvariantOrthogonal
open Filter Topology
open scoped ComplexConjugate Pointwise
universe u v
variable {G : Type u} {H : Type v} [Group G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H]
omit [InnerProductSpace ℂ H]
namespace SoficGroups.KunThomInvariantOrthogonal
theorem _root_.solution
    {X : Type*} (S : Finset X) (f : X → H)
    (a b : X) (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b)
    (r : ℝ) (hnorm : ∀ s ∈ S, ‖f s‖ = r) :
    ‖∑ s ∈ S, f s‖ ≤
      ‖f a + f b‖ + ((S.card : ℝ) - 2) * r := by
  classical
  let T : Finset X := (S.erase a).erase b
  have hb' : b ∈ S.erase a :=
    Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩
  have hsum :
      (∑ s ∈ S, f s) = f a + f b + ∑ s ∈ T, f s := by
    calc
      (∑ s ∈ S, f s) = f a + ∑ s ∈ S.erase a, f s :=
        (Finset.add_sum_erase S f ha).symm
      _ = f a + (f b + ∑ s ∈ T, f s) := by
        congr 1
        exact (Finset.add_sum_erase (S.erase a) f hb').symm
      _ = f a + f b + ∑ s ∈ T, f s := by abel
  have hcard : (T.card : ℝ) = (S.card : ℝ) - 2 := by
    dsimp [T]
    rw [Finset.cast_card_erase_of_mem hb',
      Finset.cast_card_erase_of_mem ha]
    ring
  have htail : (∑ s ∈ T, ‖f s‖) = (T.card : ℝ) * r := by
    calc
      (∑ s ∈ T, ‖f s‖) = ∑ _s ∈ T, r := by
        apply Finset.sum_congr rfl
        intro s hs
        exact hnorm s
          (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hs))
      _ = (T.card : ℝ) * r := by simp
  calc
    ‖∑ s ∈ S, f s‖ = ‖(f a + f b) + ∑ s ∈ T, f s‖ := by
      rw [hsum]
    _ ≤ ‖f a + f b‖ + ‖∑ s ∈ T, f s‖ :=
      norm_add_le _ _
    _ ≤ ‖f a + f b‖ + ∑ s ∈ T, ‖f s‖ := by
      exact add_le_add (le_refl _) (norm_sum_le T f)
    _ = ‖f a + f b‖ + (T.card : ℝ) * r := by rw [htail]
    _ = ‖f a + f b‖ + ((S.card : ℝ) - 2) * r := by
      rw [hcard]
end SoficGroups.KunThomInvariantOrthogonal
