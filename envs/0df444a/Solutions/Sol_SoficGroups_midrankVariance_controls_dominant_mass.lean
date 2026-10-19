-- Prove2me | solution 1 for SoficGroups.midrankVariance_controls_dominant_mass
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:52.29415+00:00
-- url     : https://prove2.me/submissions/40c6e9c4-9d40-4afa-adac-201fe5648ad9

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_midrankVariance_eq
import Theorems.Thm_SoficGroups_cube_sum_le_dominant_mass

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution
    (ps : List ℝ) (m : ℝ)
    (hsum : ps.sum = 1)
    (hpos : ∀ p ∈ ps, 0 ≤ p)
    (hdom : ∀ p ∈ ps, p ≤ m) :
    (1 - m) / 12 ≤ midrankVariance ps := by
  rw [midrankVariance_eq ps hsum]
  have hcube := cube_sum_le_dominant_mass ps m hsum hpos hdom
  linarith
end SoficGroups
