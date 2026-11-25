-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inr_b8e1d836d329
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:33:54.106123+00:00
-- url     : https://prove2.me/submissions/a810b57b-2982-4943-b7de-2a0e2deea3cd

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Examples₂ Formalism.BasicNotions.Examples₂.CD
open MeasureTheory Matrix Formalism.REAL Formalism.UG.P Topology
open scoped ENNReal NNReal
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (j) : ε (e0 ε (Sum.inr j)) = false := by
  show ε (((Fintype.equivFin {i // ¬ ε i = true}).symm j : {i // ¬ ε i = true}) : Fin n) = false
  simpa using ((Fintype.equivFin {i // ¬ ε i = true}).symm j).2
end Formalism.BasicNotions.Examples₂.CD
