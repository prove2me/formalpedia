-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_mem_cplxPts
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:51:54.827038+00:00
-- url     : https://prove2.me/submissions/08cd7a7a-930c-46d3-9bc5-c58fe738b9a9

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Finset
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {Y : Type*} [AddCommGroup Y] [Module ℂ Y]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {B : Finset ℝ} {z : ℂ} : z ∈ dc_cplxPts B ↔ ∃ b ∈ B, (b : ℂ) = z := by
  simp [dc_cplxPts]
end ReciprocityTheory.ChartRestriction.DS
