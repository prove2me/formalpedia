-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.transvection_inv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:42:36.08185+00:00
-- url     : https://prove2.me/submissions/cd0cebd0-30a3-434f-9ad5-299a8f3469e0

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
theorem _root_.solution (i j : Fin n) (hij : i ≠ j) (c : ℂ) :
    (Matrix.transvection i j c)⁻¹ = Matrix.transvection i j (-c) := by
  apply Matrix.inv_eq_right_inv
  have h := Matrix.transvection_mul_transvection_same (i := i) (j := j) hij c (-c)
  rwa [add_neg_cancel, Matrix.transvection_zero] at h
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
