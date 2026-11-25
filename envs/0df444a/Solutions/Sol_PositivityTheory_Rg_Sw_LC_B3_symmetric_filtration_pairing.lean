-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.symmetric_filtration_pairing
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T11:56:41.506143+00:00
-- url     : https://prove2.me/submissions/329d1581-ee04-44af-8102-c08eb5559d32

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_mul
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_sum
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_symmetric_filtration_generator

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
theorem _root_.solution (ε : Fin m → Bool) (a b : Fin m) : SymbolInFirstFamily ε (pairSym (n := n) ε a b) := by
  unfold pairSym
  refine symmetric_filtration_sum _ _ fun i _ => symmetric_filtration_mul ?_ ?_
  · unfold vecVar; split_ifs with h <;> exact symmetric_filtration_generator ε _ (by simp [S1, inF1, h])
  · unfold covVar; split_ifs with h <;> exact symmetric_filtration_generator ε _ (by simp [S1, inF1, h])
end PositivityTheory.Rg.Sw.LC.B3
