-- Prove2me | solution 1 for PositivityTheory.CW.MaximumPrincipleOneFunction.hilbert_schmidt_nonneg_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:35.657167+00:00
-- url     : https://prove2.me/submissions/a3bf3c5a-78ae-4199-ae64-c247d478e7b1

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_MaximumPrincipleOfFacts

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
open PositivityTheory.CW.MaximumPrincipleOneFunction
variable {n : ℕ}
namespace PositivityTheory.CW.MaximumPrincipleOneFunction
theorem _root_.solution (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity
end PositivityTheory.CW.MaximumPrincipleOneFunction
