-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_ball_meas_50812612218f
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:40:31.233134+00:00
-- url     : https://prove2.me/submissions/8223d3ad-26ef-4cfd-b831-27da392e899f

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_hsG_cont_78d108c224a1

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (R : ℝ) : MeasurableSet {a : UJ ε | hsG a ≤ R} :=
  (isClosed_le (hsG_cont ε) continuous_const).measurableSet
end Formalism.BasicNotions.Examples₂.CD
