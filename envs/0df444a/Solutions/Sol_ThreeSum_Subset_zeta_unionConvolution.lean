-- Prove2me | solution 1 for ThreeSum.Subset.zeta_unionConvolution
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-03T07:20:11.425646+00:00
-- url     : https://prove2.me/submissions/25692acd-e8e0-4704-b7a8-2c588f88e8e9

import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega
import Aesop
import Definitions.Def_Submission_ThreeSum_Subset
namespace ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
private theorem powerset_subset_of_subset {u q : Finset α} (h : u ⊆ q) :
    u.powerset ⊆ q.powerset := by
  intro s hs
  exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hs).trans h)
private theorem unionConvolution_extend (f g : Finset α → ℤ)
    {u q : Finset α} (hu : u ⊆ q) :
    unionConvolution f g u =
      ∑ s ∈ q.powerset, ∑ v ∈ q.powerset,
        if s ∪ v = u then f s * g v else 0 := by
  have hp := powerset_subset_of_subset hu
  unfold unionConvolution
  calc
    _ = ∑ s ∈ u.powerset, ∑ v ∈ q.powerset,
          if s ∪ v = u then f s * g v else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_subset hp
      intro v hv hvu
      have hne : s ∪ v ≠ u := by
        intro he
        apply hvu
        apply Finset.mem_powerset.mpr
        rw [← he]
        exact Finset.subset_union_right
      simp only [hne, ite_false]
    _ = _ := by
      apply Finset.sum_subset hp
      intro s hs hsu
      apply Finset.sum_eq_zero
      intro v hv
      have hne : s ∪ v ≠ u := by
        intro he
        apply hsu
        apply Finset.mem_powerset.mpr
        rw [← he]
        exact Finset.subset_union_left
      simp only [hne, ite_false]
end ThreeSum.Subset
set_option autoImplicit false
open ThreeSum ThreeSum.Subset
open scoped BigOperators
variable {α : Type*} [DecidableEq α]
namespace ThreeSum.Subset
theorem _root_.solution (f g : Finset α → ℤ) (q : Finset α) :
    zeta (unionConvolution f g) q = zeta f q * zeta g q := by
  unfold zeta
  calc
    _ = ∑ u ∈ q.powerset, ∑ s ∈ q.powerset, ∑ v ∈ q.powerset,
          if s ∪ v = u then f s * g v else 0 := by
      apply Finset.sum_congr rfl
      intro u hu
      exact unionConvolution_extend f g (Finset.mem_powerset.mp hu)
    _ = ∑ s ∈ q.powerset, ∑ v ∈ q.powerset, ∑ u ∈ q.powerset,
          if s ∪ v = u then f s * g v else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      rw [Finset.sum_comm]
    _ = ∑ s ∈ q.powerset, ∑ v ∈ q.powerset, f s * g v := by
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro v hv
      have huv : s ∪ v ∈ q.powerset :=
        Finset.mem_powerset.mpr
          (Finset.union_subset (Finset.mem_powerset.mp hs) (Finset.mem_powerset.mp hv))
      rw [Finset.sum_eq_single (s ∪ v)]
      · simp
      · intro u hu hne
        simp only [Ne.symm hne, ite_false]
      · intro h
        exact False.elim (h huv)
    _ = _ := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
end ThreeSum.Subset
