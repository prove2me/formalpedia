-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.dc_lagrange_eig
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T11:38:56.986858+00:00
-- url     : https://prove2.me/submissions/bb380963-798c-420c-af25-bbc1ba251172

import Mathlib
import Definitions.Def_Lemmata_PowerApplication_PowApp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_DecompA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_dc_mem_cplxPts
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
theorem _root_.solution (hP : ∀ f ∈ S, aeval T (Lagrange.nodal (dc_cplxPts B) id) f = 0) :
    ∀ z : ℂ, ∀ f ∈ S, f ≠ 0 → T f = z • f → ∃ b ∈ B, z = ((b : ℝ) : ℂ) := by
  intro z f hf h0 he
  by_contra hno
  refine h0 (dc_eq_zero_of_eigen_not_mem hP (fun hz => hno ?_) hf he)
  obtain ⟨b, hb, e⟩ := dc_mem_cplxPts.mp hz
  exact ⟨b, hb, e.symm⟩
end ReciprocityTheory.ChartRestriction.DS
