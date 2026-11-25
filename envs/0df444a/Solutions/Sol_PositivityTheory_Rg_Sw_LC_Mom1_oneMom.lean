-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.LC.Mom1.oneMom
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:23.242637+00:00
-- url     : https://prove2.me/submissions/5310c4ae-c2a3-44f6-b859-7054c9f7d866

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_OneMom
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_PolynomialDerivatives_IntegrableRpowGauss
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_integrable_integrand
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_integral_diag
import Theorems.Thm_PositivityTheory_Rg_Sw_LC_Mom1_integral_offdiag

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Real
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.LC PositivityTheory.Rg.Sw.LC.Mom1
namespace PositivityTheory.Rg.Sw.LC.Mom1
theorem _root_.solution : OneMom := by
  intro c hc p q
  refine ⟨integrable_integrand c hc p q, ?_⟩
  split_ifs with h
  · subst h; exact integral_diag c hc p
  · exact integral_offdiag c p q h
end PositivityTheory.Rg.Sw.LC.Mom1
