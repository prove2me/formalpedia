-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.etaEq_pair
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:03:20.523712+00:00
-- url     : https://prove2.me/submissions/47dc0f6d-e24c-4398-bdc1-0701d1fad527

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaEq_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaEq_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaEq_X_inl
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaEq_X_inr

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
theorem _root_.solution (ε : Fin m → Bool) (a b : Fin m) : EtaEq (pairSym (n := n) ε a b) (pdeg ε a b) := by
  unfold pairSym pdeg
  apply etaEq_sum
  intro i _
  apply etaEq_mul
  · unfold vecVar
    split_ifs <;> simp [etaEq_X_inl, etaEq_X_inr]
  · unfold covVar
    split_ifs <;> simp [etaEq_X_inl, etaEq_X_inr]
end PositivityTheory.Rg.Sw.LC.B3
