-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.NullS.norm_gs_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T11:54:40.694074+00:00
-- url     : https://prove2.me/submissions/c0661f08-e631-414a-b675-c3cbe38deaf0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_HasFDerivAtEvX
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SquareNormBound
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PolyExpBound
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_NullS_sq_norm_le
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
theorem _root_.solution (c : ℝ) (hc : 0 < c) (x : Fin m → Fin n → ℂ) : ‖gs c x‖ ≤ Real.exp (-(c * ‖x‖ ^ 2)) := by
  unfold gs
  rw [show (-(↑(c * ∑ a, ∑ i, ‖x a i‖ ^ 2) : ℂ)) = ↑(-(c * ∑ a, ∑ i, ‖x a i‖ ^ 2)) by push_cast; ring,
    Complex.norm_exp_ofReal]
  apply Real.exp_le_exp.2
  have := sq_norm_le x
  nlinarith
end PositivityTheory.Rg.Sw.LC.NullS
