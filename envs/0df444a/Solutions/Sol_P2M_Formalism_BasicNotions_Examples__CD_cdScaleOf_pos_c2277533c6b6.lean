-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_pos_c2277533c6b6
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T17:08:06.412964+00:00
-- url     : https://prove2.me/submissions/a6e06045-7ebd-4931-81f3-f68ad989a864

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inl_4ae9369d95e2
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inr_b8e1d836d329
import Theorems.Thm_P2M_Formalism_BasicNotions_Examples__CD_cdScaleOf_spec_07daed5ec9cb

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
variable (C : CDHaar)
namespace Formalism.BasicNotions.Examples₂.CD
theorem _root_.solution (n : ℕ) (ε : Fin n → Bool) : 0 < cdScaleOf C n ε :=
  (cdScaleOf_spec C ε (e0 ε) (sign_split_equiv_inl ε) (sign_split_equiv_inr ε)).1
end Formalism.BasicNotions.Examples₂.CD
