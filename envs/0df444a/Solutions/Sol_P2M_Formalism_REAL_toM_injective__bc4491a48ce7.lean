-- Prove2me | solution 1 for P2M_Formalism_REAL_toM_injective__bc4491a48ce7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:47:31.500458+00:00
-- url     : https://prove2.me/submissions/35031e83-5275-4ea5-a862-5d5e76076e8d

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothOnGVIff
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CompactHaarRightInvariantInst

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory MeasureTheory.Measure
noncomputable section
open Formalism Formalism.REAL
namespace Formalism.REAL
theorem _root_.solution {n : ℕ} {ε : Fin n → Bool} {g h : UJ ε} (hgh : toM g = toM h) : g = h := by
  exact Subtype.ext (Units.ext hgh)
end Formalism.REAL
