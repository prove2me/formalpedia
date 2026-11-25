-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.pair_comm_K
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:54.485069+00:00
-- url     : https://prove2.me/submissions/d08deb64-6ce3-48ee-99c5-a4269bb1de69

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symK_pair
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B1_op_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_eq_opL
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_op_zero
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_CoreBb_symK_op


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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.B3
open PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.B3
theorem _root_.solution (ε : Fin m → Bool) (a b : Fin m) (i j : Fin n) :
    opL (pairSym (n := n) ε a b) * KopL ε i j = KopL ε i j * opL (pairSym (n := n) ε a b) := by
  refine LinearMap.ext fun f => ?_
  have h := symK_op ε i j (pairSym (n := n) ε a b) f
  rw [symK_pair, op_zero] at h
  simp only [Module.End.mul_apply, ← op_eq_opL]
  exact (sub_eq_zero.1 h.symm).symm
end PositivityTheory.Rg.Sw.LC.B3
