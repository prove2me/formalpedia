-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_lagrange_decomp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:34:16.387319+00:00
-- url     : https://prove2.me/submissions/cd641994-1448-45d1-8765-968fa67e3586

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_injOn_id_cplx
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_mem_cplxPts
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_aeval_mem
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_basis_eigen

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
    (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) :
    ∀ f ∈ S, ∃ fb : ℝ → Y, (∀ b, fb b ∈ S ∧ T (fb b) = ((b : ℝ) : ℂ) • fb b) ∧ f = ∑ b ∈ B, fb b := by
  classical
  intro f hf
  refine ⟨fun b => if b ∈ B then aeval T (Lagrange.basis (dc_cplxPts B) id (b : ℂ)) f else 0, fun b => ?_, ?_⟩
  · by_cases hb : b ∈ B
    · simp only [hb, if_true]
      exact ⟨dc_aeval_mem hT _ f hf, dc_basis_eigen hP (dc_mem_cplxPts.mpr ⟨b, hb, rfl⟩) f hf⟩
    · simp [hb]
  · rcases B.eq_empty_or_nonempty with hB | hB
    · subst hB
      have := hP f hf
      simpa [dc_cplxPts, Lagrange.nodal] using this
    · rw [Finset.sum_congr rfl fun b hb => if_pos hb]
      have hs : (dc_cplxPts B).Nonempty := hB.image _
      have h1 := Lagrange.sum_basis (dc_injOn_id_cplx B) hs
      have h2 : ∑ b ∈ B, aeval T (Lagrange.basis (dc_cplxPts B) id (b : ℂ)) f =
          ∑ z ∈ dc_cplxPts B, aeval T (Lagrange.basis (dc_cplxPts B) id z) f := by
        rw [dc_cplxPts, Finset.sum_image fun x _ y _ h => Complex.ofReal_injective h]
      rw [h2, ← LinearMap.sum_apply, ← map_sum, h1, map_one, Module.End.one_apply]
end ReciprocityTheory.ChartRestriction.DS
