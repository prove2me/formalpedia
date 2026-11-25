-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_basis_eigen
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:27:22.083993+00:00
-- url     : https://prove2.me/submissions/179c7652-89eb-433a-a470-b788db19194b

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_X_sub_mul_basis

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
theorem _root_.solution (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) {z : ℂ}
    (hz : z ∈ dc_cplxPts B) : ∀ f ∈ S, T (aeval T (Lagrange.basis (dc_cplxPts B) id z) f) =
      z • aeval T (Lagrange.basis (dc_cplxPts B) id z) f := by
  intro f hf
  have h := congrArg (fun p => aeval T p f) (dc_X_sub_mul_basis hz)
  simp only [map_mul, Module.End.mul_apply, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
    Module.algebraMap_end_apply, hP f hf, map_zero] at h
  exact sub_eq_zero.mp h
end ReciprocityTheory.ChartRestriction.DS
