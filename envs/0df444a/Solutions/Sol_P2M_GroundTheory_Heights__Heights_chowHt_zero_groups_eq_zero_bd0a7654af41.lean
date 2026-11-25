-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_eq_zero_bd0a7654af41
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:55.277295+00:00
-- url     : https://prove2.me/submissions/e5341e3e-980d-4fb2-8842-163ea80e0198

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowDegree
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LowerBoundConditional
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHt_zero_groups_77d7baeecfd0
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowHeightConst_8b6933d50429


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory NumberField
noncomputable section
variable {K : Type} [Field K] [NumberField K] {n : ℕ}
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution (H : ArchData K n) (δ : ℕ) {g : MvPolynomial (Fin 0 × Fin n) K}
    (hg : g ≠ 0) : chowHt H 0 δ g = 0 := by
  rw [chowHt_zero_groups, eq_C_of_isEmpty g]
  rw [eq_C_of_isEmpty g] at hg
  exact chowHeightConst K n 0 H _ fun h => hg (by rw [h, map_zero])
end GroundTheory.Heights₂.Heights
