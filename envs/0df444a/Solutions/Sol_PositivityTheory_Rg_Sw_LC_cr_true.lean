-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.cr_true
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:18:17.841604+00:00
-- url     : https://prove2.me/submissions/dd11b1d2-caf3-4a4d-835a-acb9742d34d9

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_NullStableAlt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HopPderivComm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (c : ℝ) (a : Fin m) (i : Fin n) (Q : PX m n) :
    cr c (a, i, true) Q = -pderiv (a, i, true) Q + (2 * c : ℂ) • (X (a, i, false) * Q) := by
  simp [cr]
end PositivityTheory.Rg.Sw.LC
