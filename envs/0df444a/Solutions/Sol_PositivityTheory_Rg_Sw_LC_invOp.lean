-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.invOp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T13:26:54.124176+00:00
-- url     : https://prove2.me/submissions/8a607720-3012-437b-bbfd-97ed7bc3e573

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_SymmetricFiltrationIffSupported
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_MapDomainInlInr
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_TransvectionInv
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_InvOp
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_B3_invOp_of
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialDifferentialOperators_compSt
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_PolynomialWeightAction_fftSym
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_compSt
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_fftSym


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC
namespace PositivityTheory.Rg.Sw.LC
theorem _root_.solution : InvOp := B3.invOp_of compSt fftSym
end PositivityTheory.Rg.Sw.LC
