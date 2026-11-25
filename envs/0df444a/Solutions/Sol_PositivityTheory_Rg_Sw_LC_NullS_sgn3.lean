-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.sgn3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:52:36.743133+00:00
-- url     : https://prove2.me/submissions/768f52a1-09d8-459f-88e1-28a0d090f70a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PartialDerivQuadraticPairing
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SumPderivXMem
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_sgn_mul_self


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.NullS
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.NullS
theorem _root_.solution (ε : Fin m → Bool) (a : Fin m) :
    (C (sgn ε a) : PX m n) * (C (sgn ε a) * C (sgn ε a)) = C (sgn ε a) := by
  rw [← map_mul, sgn_mul_self, map_one, mul_one]
end PositivityTheory.Rg.Sw.LC.NullS
