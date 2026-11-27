-- Prove2me | solution 1 for PositivityTheory.Mirab.Dim.psiExt_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:41:04.156396+00:00
-- url     : https://prove2.me/submissions/54b1db18-d46f-4162-8faa-f4f6125c76c2

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndDim
import Theorems.Thm_PositivityTheory_Mirab_Dim_psiExt_of_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory.FiniteGL Formalism.L2.Indef.Tree Formalism.EigenvalueLevelCeiling
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Dim
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
variable (ψ₀ : AddChar k ℂ)
namespace PositivityTheory.Mirab.Dim
theorem _root_.solution : psiExt n ψ₀ 1 = 1 := by
  have h := psiExt_of_mem n ψ₀ 1
  rw [OneMemClass.coe_one, map_one] at h
  exact h
end PositivityTheory.Mirab.Dim
