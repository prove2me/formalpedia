-- Prove2me | solution 1 for ReciprocityTheory.AnForm.P.cellMat_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:54:48.228155+00:00
-- url     : https://prove2.me/submissions/4343a6e0-10f7-467d-bcd3-3a6dbf4385d3

import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensA
import Definitions.Def_ReciprocityTheory_AnalyticForms_LeviForms_HomDensB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.AnForm ReciprocityTheory.AnForm.P
open Polynomial Matrix
noncomputable section
namespace ReciprocityTheory.AnForm.P
theorem _root_.solution (N : ℕ) (z : Pairs N → ℂ) :
    cellMat N z = ∑ k ∈ Finset.range N, ((k.factorial : ℂ)⁻¹) • zMat N z ^ k := rfl
end ReciprocityTheory.AnForm.P
