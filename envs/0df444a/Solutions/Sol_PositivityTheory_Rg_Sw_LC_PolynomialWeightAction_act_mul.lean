-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.PolynomialWeightAction.act_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:46.386708+00:00
-- url     : https://prove2.me/submissions/b1c600ba-806f-444a-af17-2d73d6281b5a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_act_comp

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
theorem _root_.solution (A B : Matrix (Fin n) (Fin n) ℂ) (q : MvPolynomial (FinalTheorems m n) ℂ) :
    act (A * B) q = act B (act A q) := by
  rw [act_comp]; rfl
end PositivityTheory.Rg.Sw.LC.PolynomialWeightAction
