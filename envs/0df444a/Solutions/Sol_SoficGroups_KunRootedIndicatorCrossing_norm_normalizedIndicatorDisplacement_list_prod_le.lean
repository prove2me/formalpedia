-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.norm_normalizedIndicatorDisplacement_list_prod_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:55.923416+00:00
-- url     : https://prove2.me/submissions/b61a5772-80b1-4216-a975-0d78db2ca617

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_norm_normalizedIndicatorDisplacement_generator_le
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedIndicatorDisplacement_mul

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (hf : ∀ x, f x = 0 ∨ f x = 1)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) (w : List ι) :
    ‖normalizedIndicatorDisplacement p f (w.map p).prod‖ ≤
      (Fintype.card ι : ℝ) * w.length := by
  induction w with
  | nil =>
      simp [normalizedIndicatorDisplacement]
  | cons i w ih =>
      rw [List.map_cons, List.prod_cons,
        normalizedIndicatorDisplacement_mul]
      calc
        ‖normalizedIndicatorDisplacement p f (p i) +
          permutationUnitary (p i)
            (normalizedIndicatorDisplacement p f (w.map p).prod)‖ ≤
            ‖normalizedIndicatorDisplacement p f (p i)‖ +
              ‖permutationUnitary (p i)
                (normalizedIndicatorDisplacement p f (w.map p).prod)‖ :=
          norm_add_le _ _
        _ = ‖normalizedIndicatorDisplacement p f (p i)‖ +
              ‖normalizedIndicatorDisplacement p f (w.map p).prod‖ := by
          rw [(permutationUnitary (p i)).norm_map]
        _ ≤ (Fintype.card ι : ℝ) +
              (Fintype.card ι : ℝ) * w.length :=
          add_le_add
            (norm_normalizedIndicatorDisplacement_generator_le
              p f hf hdefect i) ih
        _ = (Fintype.card ι : ℝ) * (i :: w).length := by
          simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
          ring
end SoficGroups.KunRootedIndicatorCrossing
