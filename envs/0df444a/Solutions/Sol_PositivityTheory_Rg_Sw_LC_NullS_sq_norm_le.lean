-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.sq_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:44:22.588447+00:00
-- url     : https://prove2.me/submissions/f123ff9d-73fa-4119-851f-5aa868270ce1

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HasFDerivAtEvX
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SquareNormBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound
import Theorems.Thm_UpperTheory_Reformulated_B_SquareNormBound_sq_norm_le


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
theorem _root_.solution (x : Fin m → Fin n → ℂ) : ‖x‖ ^ 2 ≤ ∑ a, ∑ i, ‖x a i‖ ^ 2 :=
  _root_.UpperTheory.Reformulated.B.SquareNormBound.sq_norm_le x
end PositivityTheory.Rg.Sw.LC.NullS
