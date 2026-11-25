-- Prove2me | solution 1 for PositivityTheory.CW.HilbertSchmidtNorm.hilbert_schmidt_nonneg_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T11:25:27.203958+00:00
-- url     : https://prove2.me/submissions/748ba10d-506e-4f2f-8f8c-46f44039d41a

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_SecondDerivativeHolds

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset ReciprocityTheory.ChartRestriction.DS
open PositivityTheory PositivityTheory.CW
open PositivityTheory.CW.HilbertSchmidtNorm
variable {n : ℕ}
namespace PositivityTheory.CW.HilbertSchmidtNorm
theorem _root_.solution (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
end PositivityTheory.CW.HilbertSchmidtNorm
