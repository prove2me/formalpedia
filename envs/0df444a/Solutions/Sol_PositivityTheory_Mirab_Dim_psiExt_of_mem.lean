-- Prove2me | solution 1 for PositivityTheory.Mirab.Dim.psiExt_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:34:07.138241+00:00
-- url     : https://prove2.me/submissions/993237b5-c40c-41e2-97ae-14e524235c8d

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndDim

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
theorem _root_.solution (u : uniSub k n) : psiExt n ψ₀ (u : mirabSub k n) = genericChar n ψ₀ u := by
  unfold psiExt
  rw [dif_pos u.2]
end PositivityTheory.Mirab.Dim
