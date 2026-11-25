-- Prove2me | solution 1 for PositivityTheory.CW.PMaxPr.hilbert_schmidt_nonneg_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T11:29:37.514357+00:00
-- url     : https://prove2.me/submissions/bdf92e57-2c57-4b59-8f46-cce58f30a14d

import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_FunctionalCalculusLaws
import Definitions.Def_Development_WeilBound_CoreStatements_PublishedTheorems_CasselmanWallach_PMaxPr

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
open PositivityTheory.CW.PMaxPr
namespace PositivityTheory.CW.PMaxPr
theorem _root_.solution {n : ℕ} (g : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs2 g :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _
end PositivityTheory.CW.PMaxPr
