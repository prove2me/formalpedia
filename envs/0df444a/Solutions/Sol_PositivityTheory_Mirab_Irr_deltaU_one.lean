-- Prove2me | solution 1 for PositivityTheory.Mirab.Irr.deltaU_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T18:20:25.317911+00:00
-- url     : https://prove2.me/submissions/37a5217f-5b21-48c3-8ed1-03beabeb1fd7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_PublishedFoundations_BlockTriangularOfSubOne
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Development_WeilBound_CoreStatements_RegularisedThetaMirabolic_CuspidalMirabolic_IndIrr

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
open PositivityTheory PositivityTheory.Mirab PositivityTheory.Mirab.Irr
variable {k : Type} [Field k] [Fintype k] (n : ℕ)
namespace PositivityTheory.Mirab.Irr
theorem _root_.solution (ψ₀ : AddChar k ℂ) : deltaU n ψ₀ 1 = 1 := by
  unfold deltaU
  rw [dif_pos (one_mem _)]
  exact map_one (genericChar n ψ₀)
end PositivityTheory.Mirab.Irr
