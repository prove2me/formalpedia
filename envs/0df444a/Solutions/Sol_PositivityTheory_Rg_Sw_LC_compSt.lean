-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.compSt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T13:15:39.528602+00:00
-- url     : https://prove2.me/submissions/1e0e6b52-f5e8-4468-90be-46b1bbe6cc94

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_FirstFamilySymbolMulVariablePow
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainInlInr
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_compSt

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
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution : PositivityTheory.Rg.Sw.LC.CompSt := PositivityTheory.Rg.Sw.LC.PolynomialDifferentialOperators.compSt
end PositivityTheory.Rg.Sw.LC
