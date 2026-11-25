-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_sign_split_equiv_inl_4ae9369d95e2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:29:04.732784+00:00
-- url     : https://prove2.me/submissions/a4737c70-470d-40f9-a48c-9c59e7b21f2e

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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) (i) : ε (e0 ε (Sum.inl i)) = true := by
  simp only [e0, Equiv.trans_apply, Equiv.sumCongr_apply, Sum.map_inl, Equiv.sumCompl_apply_inl]
  exact ((Fintype.equivFin {i // ε i = true}).symm i).2
end Formalism.BasicNotions.Examples₂.CD
