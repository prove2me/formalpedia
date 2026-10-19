-- Prove2me | solution 1 for SoficGroups.ExceptionalRankOffset.rankDropCount_le_goodSubtype_add_exceptions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/d62b1562-1b7c-4166-bb9a-1bae45909a8e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ExceptionalRankOffset_rankDropCount_goodSubtype_eq

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.ExceptionalRankOffset
open Filter Topology
open scoped BigOperators
namespace SoficGroups.ExceptionalRankOffset
theorem _root_.solution
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (G : Finset ι) (u v : ι → ℝ) (H r : ℝ) :
    SoficGroups.rankDropCount u v H r ≤
      SoficGroups.rankDropCount
          (fun i : {i // i ∈ G} => u i.1)
          (fun i : {i // i ∈ G} => v i.1) H r +
        (((Finset.univ : Finset ι) \ G).card : ℝ) := by
  classical
  let d : ι → ℝ := fun i =>
    if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then 1 else 0
  have hgood :
      SoficGroups.rankDropCount
        (fun i : {i // i ∈ G} => u i.1)
        (fun i : {i // i ∈ G} => v i.1) H r =
        ∑ i ∈ G, d i := by
    exact rankDropCount_goodSubtype_eq G u v H r
  have hfull : SoficGroups.rankDropCount u v H r = ∑ i : ι, d i := by
    rfl
  have hsplit :
      (∑ i ∈ (Finset.univ : Finset ι) \ G, d i) +
        (∑ i ∈ G, d i) = ∑ i : ι, d i :=
    Finset.sum_sdiff (Finset.subset_univ G)
  have hbad :
      (∑ i ∈ (Finset.univ : Finset ι) \ G, d i) ≤
        (((Finset.univ : Finset ι) \ G).card : ℝ) := by
    calc
      (∑ i ∈ (Finset.univ : Finset ι) \ G, d i) ≤
        ∑ _i ∈ (Finset.univ : Finset ι) \ G, (1 : ℝ) := by
          apply Finset.sum_le_sum
          intro i hi
          dsimp [d]
          split_ifs <;> norm_num
      _ = (((Finset.univ : Finset ι) \ G).card : ℝ) := by simp
  rw [hfull, hgood]
  linarith
end SoficGroups.ExceptionalRankOffset
