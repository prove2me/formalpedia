-- Prove2me | solution 1 for SoficGroups.normalizedHamming_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/9b7447b5-5c29-47bd-bc81-fde5bc9ab790

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {Y : Type*} [Fintype Y] [DecidableEq Y]
    (p q : Equiv.Perm Y) : normalizedHamming p q ≤ 1 := by
  have hcard :
      hammingDist (fun y => p y) (fun y => q y) ≤ Fintype.card Y :=
    hammingDist_le_card_fintype
  unfold normalizedHamming
  calc
    (hammingDist (fun y => p y) (fun y => q y) : ℝ) / Fintype.card Y ≤
        (Fintype.card Y : ℝ) / Fintype.card Y := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast hcard
      · positivity
    _ ≤ 1 := by
      by_cases h : Fintype.card Y = 0 <;> simp [h]
end SoficGroups
