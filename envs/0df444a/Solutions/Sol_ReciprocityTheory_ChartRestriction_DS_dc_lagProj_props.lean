-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_lagProj_props
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:09.306227+00:00
-- url     : https://prove2.me/submissions/0391e876-365b-4809-b7d4-398ea28a4ab2

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_injOn_id_cplx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_aeval_eigen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_basis_eigen
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_eq_zero_of_eigen_not_mem

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
theorem _root_.solution (hT : ∀ f ∈ S, T f ∈ S)
    (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) (z : ℂ) :
    (∀ f ∈ S, dc_lagProj T B z (dc_lagProj T B z f) = dc_lagProj T B z f) ∧
      (∀ f ∈ S, T (dc_lagProj T B z f) = z • dc_lagProj T B z f) ∧
      (∀ f ∈ S, T f = z • f → dc_lagProj T B z f = f) ∧
      ∀ f ∈ S, ∀ z' : ℂ, z' ≠ z → T f = z' • f → dc_lagProj T B z f = 0 := by
  classical
  by_cases hz : z ∈ dc_cplxPts B
  · simp only [dc_lagProj, hz, if_true]
    refine ⟨fun f hf => ?_, dc_basis_eigen hP hz, fun f hf he => ?_, fun f hf z' hz' he => ?_⟩
    · rw [dc_aeval_eigen (dc_basis_eigen hP hz f hf)]
      have := Lagrange.eval_basis_self (v := id) (dc_injOn_id_cplx B) hz
      simp only [id] at this
      rw [this, one_smul]
    · rw [dc_aeval_eigen he]
      have := Lagrange.eval_basis_self (v := id) (dc_injOn_id_cplx B) hz
      simp only [id] at this
      rw [this, one_smul]
    · by_cases hz'' : z' ∈ dc_cplxPts B
      · rw [dc_aeval_eigen he]
        have := Lagrange.eval_basis_of_ne (v := id) (s := dc_cplxPts B) (Ne.symm hz') hz''
        simp only [id] at this
        rw [this, zero_smul]
      · rw [dc_eq_zero_of_eigen_not_mem hP hz'' hf he, map_zero]
  · simp only [dc_lagProj, hz, if_false, LinearMap.zero_apply]
    refine ⟨fun _ _ => trivial, fun _ _ => by simp, fun f hf he => (dc_eq_zero_of_eigen_not_mem hP hz hf he).symm,
      fun _ _ _ _ _ => trivial⟩
end ReciprocityTheory.ChartRestriction.DS
