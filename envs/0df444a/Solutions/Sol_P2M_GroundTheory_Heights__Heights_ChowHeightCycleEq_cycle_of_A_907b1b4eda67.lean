-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_cycle_of_A_907b1b4eda67
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:30:39.10139+00:00
-- url     : https://prove2.me/submissions/46c88604-2365-48c0-96c8-fed0bf5ace7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ArchOfPlacesEmbedding
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_cycle_of_mul_d4b13781df53
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ChowHeightCycleEq_additive_761cb60a5283

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
open GroundTheory.Heights₂.Heights.ChowHeightCycleEq
variable {n e : ℕ}
namespace GroundTheory.Heights₂.Heights.ChowHeightCycleEq
theorem _root_.solution (hA : ChowHeightMul.Statement) : IndefiniteRowSideFullHecke.ArithBezout.ChowHeightCycle.Statement := by
  intro K _ _ n e S hS ι Z f δ hf
  exact cycle_of_mul _ (fun f g δ₁ δ₂ hf hg => additive hA S hS f g δ₁ δ₂ hf hg) Z f δ hf
end GroundTheory.Heights₂.Heights.ChowHeightCycleEq
