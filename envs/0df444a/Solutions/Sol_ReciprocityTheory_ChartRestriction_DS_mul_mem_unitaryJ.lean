-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.mul_mem_unitaryJ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:51.440878+00:00
-- url     : https://prove2.me/submissions/ad02a9c7-e0fe-4883-83e6-0b42fa47cccc

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_AnalyticVectors_ConjTransposeEqOfInG
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_RigidityTheorems_MultOneA

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
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ε : Fin n → Bool} {g h : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε)
    (hh : h ∈ UJset ε) : g * h ∈ UJset ε := by
  show (g * h)ᴴ * Jm ε * (g * h) = Jm ε
  have hg' : gᴴ * Jm ε * g = Jm ε := hg
  have hh' : hᴴ * Jm ε * h = Jm ε := hh
  rw [Matrix.conjTranspose_mul,
    show hᴴ * gᴴ * Jm ε * (g * h) = hᴴ * (gᴴ * Jm ε * g) * h by simp only [Matrix.mul_assoc],
    hg', hh']
end ReciprocityTheory.ChartRestriction.DS
