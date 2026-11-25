-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_cond_congr_set_753e0bb205c1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:51.343264+00:00
-- url     : https://prove2.me/submissions/ed35f0a7-e217-4141-9ada-007e876c568b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SpecFirstDetFormNeZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_GaussNormEqCoeffGaussNorm

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
open MvPolynomial MeasureTheory NumberField Matrix ProbabilityTheory
noncomputable section
open GroundTheory.Heights₂.Heights.ObjectsHeight
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution {α : Type*} [MeasurableSpace α] (μ : Measure α) {s t : Set α}
    (h : s =ᵐ[μ] t) : cond μ s = cond μ t := by
  rw [ProbabilityTheory.cond, ProbabilityTheory.cond, measure_congr h, Measure.restrict_congr_set h]
end GroundTheory.Heights₂.Heights.ObjectsHeight
