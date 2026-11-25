-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.symKComm
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T12:16:56.880222+00:00
-- url     : https://prove2.me/submissions/519dd906-1c07-4353-80a8-c2f61ee6ca4a

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_CoreSt
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_ProdMapPowSingle
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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.CoreBb
open PositivityTheory.Rg.Sw
variable {m n : ℕ}
namespace PositivityTheory.Rg.Sw.LC.CoreBb
namespace _root_.PositivityTheory.Rg.Sw.LC
theorem _root_.solution : SymKComm := fun _ _ ε i j s _ f _ => symK_op ε i j s f
end _root_.PositivityTheory.Rg.Sw.LC
end PositivityTheory.Rg.Sw.LC.CoreBb
