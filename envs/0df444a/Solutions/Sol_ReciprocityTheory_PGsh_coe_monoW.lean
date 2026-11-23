-- Prove2me | solution 1 for ReciprocityTheory.PGsh.coe_monoW
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T15:26:25.208411+00:00
-- url     : https://prove2.me/submissions/477a393f-9b1a-4d11-a4a4-832b625a60f4

import Mathlib
import Definitions.Def_ReciprocityTheory_DualLattices_Eisenstein4CoeffBound
import Definitions.Def_ReciprocityTheory_DualLattices_QExpansionMonoWCoeffZero
import Theorems.Thm_ReciprocityTheory_PGsh_monoIdx_wt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.PGsh
open UpperHalfPlane hiding I
open Complex ModularForm ModularFormClass MatrixGroups EisensteinSeries
namespace ReciprocityTheory.PGsh
theorem _root_.solution {w a : ℕ} (h : a ∈ monoIdx w) :
    (⇑(monoW w a) : ℍ → ℂ) = (⇑E₄) ^ a * (⇑E₆) ^ monoB w a := by
  simp [monoW, monoIdx_wt h]
end ReciprocityTheory.PGsh
