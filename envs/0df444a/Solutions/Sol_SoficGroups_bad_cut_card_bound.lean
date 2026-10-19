-- Prove2me | solution 1 for SoficGroups.bad_cut_card_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:50.999068+00:00
-- url     : https://prove2.me/submissions/764cd0d7-3d4a-404f-8818-956d208ed750

import Mathlib
import Definitions.Def_NonSoficGroup

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
namespace SoficGroups
theorem _root_.solution {γ ell a : ℝ} {N b q : ℕ}
    (hgap : ell < γ)
    (hadd : γ * (b : ℝ) - a * (N : ℝ) ≤ (q : ℝ))
    (hbad : (q : ℝ) ≤ ell * (b : ℝ)) :
    (b : ℝ) ≤ a * (N : ℝ) / (γ - ell) := by
  apply (le_div_iff₀ (sub_pos.mpr hgap)).2
  nlinarith
end SoficGroups
