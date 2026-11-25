-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.fockMom_of_basic
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T12:37:26.081533+00:00
-- url     : https://prove2.me/submissions/3aadece2-c0c4-41b0-a65a-87fb526cbc6b

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ContrEqOfSubset
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FockMomOfBasic
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_fockMom_of
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_oneMom
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_oneMom


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
variable (hB : FockBasic)
variable (hM : OneMom)
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution (hB : FockBasic) : FockMom := fockMom_of hB oneMom
end PositivityTheory.Rg.Sw.LC
