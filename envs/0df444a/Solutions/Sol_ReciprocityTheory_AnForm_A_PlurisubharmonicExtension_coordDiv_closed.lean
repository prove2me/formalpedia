-- Prove2me | solution 1 for ReciprocityTheory.AnForm.A.PlurisubharmonicExtension.coordDiv_closed
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:50.848468+00:00
-- url     : https://prove2.me/submissions/b88ef4b9-345c-45e7-aee8-749caae5e58a

import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExtB
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshExt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Real Filter Topology MeasureTheory
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
open ReciprocityTheory.AnForm.A
variable {D : ℕ} {U : Set (Fin D → ℂ)} {S : Finset (Fin D)} {u : (Fin D → ℂ) → ℝ} {C κ : ℝ}
namespace ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
theorem _root_.solution (S : Finset (Fin D)) : IsClosed (coordDiv S) := by
  have : coordDiv S = ⋃ i ∈ S, {z : Fin D → ℂ | z i = 0} := by
    ext z; simp [coordDiv]
  rw [this]
  exact isClosed_biUnion_finset fun i _ => isClosed_eq (continuous_apply i) continuous_const
end ReciprocityTheory.AnForm.A.PlurisubharmonicExtension
