-- Prove2me | solution 1 for P2M_Formalism_BasicNotions_Examples__CD_hsG_cont_78d108c224a1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:29:44.687668+00:00
-- url     : https://prove2.me/submissions/ee56ad96-cd37-4d4a-b4ab-25ccaf1e891c

import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_HaarDensityNeZero
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_FrobeniusBoundOfMulNearOne
import Definitions.Def_Formalism_LocalRingCardinality_SpanPowerMembership_SignSplitEquivInl
import Theorems.Thm_Formalism_REAL_continuous_coeMatrix


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
theorem _root_.solution {n : ℕ} (ε : Fin n → Bool) : Continuous (hsG : UJ ε → ℝ) := by
  have h : (hsG : UJ ε → ℝ) = fun g => ∑ i, ∑ j, ‖coeMatrixAlt ε g i j‖ ^ 2 := rfl
  rw [h]
  refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
  exact (((continuous_apply j).comp ((continuous_apply i).comp (continuous_coeMatrix ε))).norm).pow 2
end Formalism.BasicNotions.Examples₂.CD
