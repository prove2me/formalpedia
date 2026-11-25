-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.B3.etaEq_sum
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:06.027204+00:00
-- url     : https://prove2.me/submissions/b3915bf8-0d7b-4221-a581-a941330c12cb

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PairSym
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_PderivPowMonomial
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaEq_add
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_etaEq_zero

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
theorem _root_.solution {ι : Type*} (T : Finset ι) (u : ι → Sym m n) {d : ℕ} (hu : ∀ i ∈ T, EtaEq (u i) d) :
    EtaEq (∑ i ∈ T, u i) d := Finset.sum_induction _ (fun r => EtaEq r d) (fun _ _ => etaEq_add) (etaEq_zero d) hu
end PositivityTheory.Rg.Sw.LC.B3
