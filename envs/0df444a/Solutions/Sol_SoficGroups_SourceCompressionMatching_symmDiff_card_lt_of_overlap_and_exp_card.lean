-- Prove2me | solution 1 for SoficGroups.SourceCompressionMatching.symmDiff_card_lt_of_overlap_and_exp_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/e7eb749e-1e67-48ec-b5fd-976b97817fbb

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceCompressionMatching_card_symmDiff_add_twice_inter

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.SourceCompressionMatching
open Filter Topology
open scoped BigOperators symmDiff
namespace SoficGroups.SourceCompressionMatching
theorem _root_.solution
    {V : Type*} [DecidableEq V]
    (C D : Finset V) (H eta : ℝ)
    (hoverlap :
      (1 - eta) * (C.card : ℝ) ≤ ((C ∩ D).card : ℝ))
    (hcard : (D.card : ℝ) < Real.exp H * (C.card : ℝ)) :
    ((C ∆ D).card : ℝ) <
      (Real.exp H - 1 + 2 * eta) * (C.card : ℝ) := by
  have hexact :
      ((C ∆ D).card : ℝ) + 2 * ((C ∩ D).card : ℝ) =
        (C.card : ℝ) + (D.card : ℝ) := by
    exact_mod_cast card_symmDiff_add_twice_inter C D
  nlinarith
end SoficGroups.SourceCompressionMatching
