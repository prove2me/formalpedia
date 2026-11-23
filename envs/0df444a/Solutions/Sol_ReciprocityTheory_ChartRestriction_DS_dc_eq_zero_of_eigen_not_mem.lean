-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_eq_zero_of_eigen_not_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:33:18.13997+00:00
-- url     : https://prove2.me/submissions/6b255ef9-96f4-4588-8c8f-3fcbcba5c714

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_aeval_eigen

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
variable {T : Module.End ℂ Y} {S : Submodule ℂ Y} {B : Finset ℝ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0)
    {z : ℂ} (hz : z ∉ dc_cplxPts B) {f : Y} (hf : f ∈ S) (he : T f = z • f) : f = 0 := by
  have h := hP f hf
  rw [dc_aeval_eigen he] at h
  refine (smul_eq_zero.mp h).resolve_left ?_
  rw [Lagrange.eval_nodal]
  exact Finset.prod_ne_zero_iff.mpr fun w hw h0 => hz (by simpa [sub_eq_zero] using (sub_eq_zero.mp h0) ▸ hw)
end ReciprocityTheory.ChartRestriction.DS
