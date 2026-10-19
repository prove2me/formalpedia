-- Prove2me | solution 1 for SoficGroups.CompletedChosenWordLocalRoot.approximate_action_list_prod_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/a0ce7cfe-0e10-42c9-9d67-dae5e040b6d9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_normalizedHamming_triangle
import Theorems.Thm_SoficGroups_normalizedHamming_mul_left

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators
namespace SoficGroups.CompletedChosenWordLocalRoot
theorem _root_.solution
    {G : Type*} [Group G]
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    (p : ∀ n, G → Equiv.Perm (V n))
    (hone : ∀ n, p n 1 = 1)
    (hmul : ∀ a g : G,
      Tendsto
        (fun n => SoficGroups.normalizedHamming
          (p n (a * g)) (p n a * p n g))
        atTop (nhds 0))
    (l : List G) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        (p n l.prod) ((l.map (p n)).prod))
      atTop (nhds 0) := by
  induction l with
  | nil =>
      simp [hone, SoficGroups.normalizedHamming_self]
  | cons a l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hupper : Tendsto
          (fun n =>
            SoficGroups.normalizedHamming
                (p n (a * l.prod)) (p n a * p n l.prod) +
              SoficGroups.normalizedHamming
                (p n l.prod) ((l.map (p n)).prod))
          atTop (nhds 0) := by
        simpa using (hmul a l.prod).add ih
      refine squeeze_zero
        (fun n => SoficGroups.normalizedHamming_nonneg _ _) ?_ hupper
      intro n
      have h := SoficGroups.normalizedHamming_triangle
        (p n (a * l.prod))
        (p n a * p n l.prod)
        (p n a * (l.map (p n)).prod)
      rw [SoficGroups.normalizedHamming_mul_left] at h
      exact h
end SoficGroups.CompletedChosenWordLocalRoot
