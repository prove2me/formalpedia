-- Prove2me | solution 1 for PositivityTheory.Rg.Sw.SP.divZ_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T11:50:39.029914+00:00
-- url     : https://prove2.me/submissions/8833a3b6-2147-4764-91e6-a5896ff444ef

import Mathlib
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDivA
import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_SiegelWeilProof_HolomorphicContinuation_MinorFormulas_CayDiv

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
open PositivityTheory PositivityTheory.Rg PositivityTheory.Rg.Sw PositivityTheory.Rg.Sw.SP
variable {n : ℕ}
namespace PositivityTheory.Rg.Sw.SP
theorem _root_.solution {i j : ℕ} {Q : Fm n} (hQ : DivZ i Q) (h : j ≤ i) : DivZ j Q := fun e =>
  (pow_dvd_pow _ h).trans (hQ e)
end PositivityTheory.Rg.Sw.SP
