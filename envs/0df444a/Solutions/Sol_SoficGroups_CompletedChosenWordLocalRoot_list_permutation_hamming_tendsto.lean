-- Prove2me | solution 1 for SoficGroups.CompletedChosenWordLocalRoot.list_permutation_hamming_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:00.272868+00:00
-- url     : https://prove2.me/submissions/b6495d2c-1c62-48ae-a507-ee0fa03293c8

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_normalizedHamming_nonneg
import Theorems.Thm_SoficGroups_KunActualSoficRootRadius_normalizedHamming_mul_le
import Theorems.Thm_SoficGroups_CompletedChosenWordLocalRoot_normalizedHamming_mul_le

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.CompletedChosenWordLocalRoot
open Filter Topology
open scoped BigOperators
namespace SoficGroups.CompletedChosenWordLocalRoot
theorem _root_.solution
    (V : ℕ → Type*)
    [∀ n, Fintype (V n)] [∀ n, DecidableEq (V n)]
    {ι : Type*}
    (σ τ : ∀ n, ι → Equiv.Perm (V n))
    (hletter : ∀ i : ι,
      Tendsto
        (fun n => SoficGroups.normalizedHamming (σ n i) (τ n i))
        atTop (nhds 0))
    (l : List ι) :
    Tendsto
      (fun n => SoficGroups.normalizedHamming
        ((l.map (σ n)).prod) ((l.map (τ n)).prod))
      atTop (nhds 0) := by
  induction l with
  | nil =>
      simp [SoficGroups.normalizedHamming_self]
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons]
      have hupper : Tendsto
          (fun n =>
            SoficGroups.normalizedHamming (σ n i) (τ n i) +
              SoficGroups.normalizedHamming
                ((l.map (σ n)).prod) ((l.map (τ n)).prod))
          atTop (nhds 0) := by
        simpa using (hletter i).add ih
      refine squeeze_zero
        (fun n => SoficGroups.normalizedHamming_nonneg _ _) ?_ hupper
      intro n
      exact normalizedHamming_mul_le
        (σ n i) (τ n i)
        ((l.map (σ n)).prod) ((l.map (τ n)).prod)
end SoficGroups.CompletedChosenWordLocalRoot
