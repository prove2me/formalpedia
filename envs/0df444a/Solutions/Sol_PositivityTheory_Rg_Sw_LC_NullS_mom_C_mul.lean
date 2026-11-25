-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.mom_C_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T11:46:36.372797+00:00
-- url     : https://prove2.me/submissions/29397602-2fe4-4902-b014-075686e5c2ba

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullOperatorEvaluation

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial MeasureTheory
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (c : ℝ) (a : ℂ) (P : PX m n) : mom c (C a * P) = a * mom c P := by
  unfold mom
  rw [← integral_const_mul]
  congr 1
  funext x
  simp only [evX, map_mul, eval_C, mul_assoc]
end PositivityTheory.Rg.Sw.LC.NullS
