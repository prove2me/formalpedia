-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.sgn_mul_same
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:48:32.196433+00:00
-- url     : https://prove2.me/submissions/c4a5a77b-6a83-47e0-9cc0-c7ba60d51ffe

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
theorem _root_.solution (ε : Fin m → Bool) {a b : Fin m} (h : ε a = ε b) : sgn ε a * sgn ε b = 1 := by
  unfold sgn; rw [h]; split_ifs <;> norm_num
end PositivityTheory.Rg.Sw.LC
