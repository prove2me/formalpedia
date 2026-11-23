-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.S7.hasDerivAt_line
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:07:16.850693+00:00
-- url     : https://prove2.me/submissions/ca8f24c4-85c0-47ed-b6bf-74084e919ae8

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_IsClosedKset
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_CasimirCoefficients_PhiCasA

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
open scoped ContDiff
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7
open ReciprocityTheory.ChartRestriction.DS
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ}
namespace ReciprocityTheory.ChartRestriction.DS.S7
theorem _root_.solution {F : Matrix (Fin n) (Fin n) ℂ → ℂ} {z : Matrix (Fin n) (Fin n) ℂ}
    (hF : DifferentiableAt ℂ F z) (v : Matrix (Fin n) (Fin n) ℂ) :
    HasDerivAt (fun t : ℂ => F (z + t • v)) (fderiv ℂ F z v) 0 := by
  have hl : HasDerivAt (fun t : ℂ => z + t • v) v 0 := by
    have h := ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add z
    rw [one_smul] at h
    exact h
  have hF' : HasFDerivAt F (fderiv ℂ F z) (z + (0 : ℂ) • v) := by
    simpa using hF.hasFDerivAt
  exact hF'.comp_hasDerivAt (0 : ℂ) hl
end ReciprocityTheory.ChartRestriction.DS.S7
