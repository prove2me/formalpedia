-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_injOn_id_cplx
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:11:08.89719+00:00
-- url     : https://prove2.me/submissions/fefec663-12bf-4e3b-b860-4883ef2d22ed

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
theorem _root_.solution (B : Finset ℝ) : Set.InjOn (id : ℂ → ℂ) (dc_cplxPts B : Set ℂ) :=
  fun _ _ _ _ h => h
end ReciprocityTheory.ChartRestriction.DS
