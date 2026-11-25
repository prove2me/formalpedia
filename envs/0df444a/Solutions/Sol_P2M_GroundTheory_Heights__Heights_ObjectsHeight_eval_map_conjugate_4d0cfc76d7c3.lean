-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ObjectsHeight_eval_map_conjugate_4d0cfc76d7c3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:44:58.642106+00:00
-- url     : https://prove2.me/submissions/40f372f7-ef74-4983-835a-858d61bccc78

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
variable {k : ℕ}
namespace GroundTheory.Heights₂.Heights.ObjectsHeight
theorem _root_.solution {K : Type*} [Field K] {ι : Type*} (σ : K →+* ℂ)
    (f : MvPolynomial ι K) (x : ι → ℂ) :
    eval x (f.map (ComplexEmbedding.conjugate σ)) =
      starRingEnd ℂ (eval (star x) (f.map σ)) := by
  rw [eval_map, eval_map, eval₂_comp_left]
  congr 1
  funext i
  simp
end GroundTheory.Heights₂.Heights.ObjectsHeight
