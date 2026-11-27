-- Prove2me | solution 1 for PositivityTheory.Mirab.Dim.cls_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T04:35:28.063937+00:00
-- url     : https://prove2.me/submissions/f46b9368-14fd-4cb7-a9c1-a30e02edcef6

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
namespace PositivityTheory.Mirab.Dim
theorem _root_.solution (u : uniSub k n) (x : mirabSub k n) : cls n ((u : mirabSub k n) * x) = cls n x := by
  unfold cls
  refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
  rw [mul_inv_rev, mul_inv_cancel_left]
  exact inv_mem u.2
end PositivityTheory.Mirab.Dim
