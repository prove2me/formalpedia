-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.toE_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:00.754024+00:00
-- url     : https://prove2.me/submissions/4e085bef-7ba5-4cdd-ae1e-83a940430a6f

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DefsRep
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_InhabRep

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset (fun _ : Fin n => true))
    (v : EH n) : ‖toEuclideanCLM (n := Fin n) (𝕜 := ℂ) g v‖ = ‖v‖ := by

  have hJ : Jm (fun _ : Fin n => true) = 1 := by
    simp [Jm]
  have hg' : gᴴ * g = 1 := by
    have h0 : gᴴ * Jm (fun _ : Fin n => true) * g = Jm (fun _ : Fin n => true) := hg
    rw [hJ, Matrix.mul_one] at h0
    exact h0
  have hg2 : g * gᴴ = 1 := mul_eq_one_comm.mp hg'
  have hu : toEuclideanCLM (n := Fin n) (𝕜 := ℂ) g ∈ unitary (EH n →L[ℂ] EH n) := by
    rw [Unitary.mem_iff]
    constructor
    · rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose, hg', map_one]
    · rw [← map_star, ← map_mul, Matrix.star_eq_conjTranspose, hg2, map_one]
  exact ContinuousLinearMap.norm_map_of_mem_unitary hu v
end ReciprocityTheory.ChartRestriction.DS
