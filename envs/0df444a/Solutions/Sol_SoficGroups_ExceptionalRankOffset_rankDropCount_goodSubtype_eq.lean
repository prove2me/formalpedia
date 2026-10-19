-- Prove2me | solution 1 for SoficGroups.ExceptionalRankOffset.rankDropCount_goodSubtype_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:53.013021+00:00
-- url     : https://prove2.me/submissions/bcda644e-eccb-4a0f-a012-9873f1d957df

import Mathlib
import Definitions.Def_NonSoficGroup

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
    {ι : Type*}
    (G : Finset ι) (u v : ι → ℝ) (H r : ℝ) :
    SoficGroups.rankDropCount
        (fun i : {i // i ∈ G} => u i.1)
        (fun i : {i // i ∈ G} => v i.1) H r =
      ∑ i ∈ G,
        if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0 := by
  classical
  unfold SoficGroups.rankDropCount
  rw [Finset.univ_eq_attach]
  change
    (∑ i ∈ G.attach,
      if ⌊(v i.1 + r) / H⌋ < ⌊(u i.1 + r) / H⌋ then (1 : ℝ) else 0) =
      ∑ i ∈ G,
        if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0
  exact Finset.sum_attach G
    (fun i : ι =>
      if ⌊(v i + r) / H⌋ < ⌊(u i + r) / H⌋ then (1 : ℝ) else 0)
end SoficGroups.ExceptionalRankOffset
