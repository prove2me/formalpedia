-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_BoundedMonomials_continuous_evalCone_7b41833d48e0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T02:36:43.890147+00:00
-- url     : https://prove2.me/submissions/96af716b-2cc1-4e01-bd7e-8a52a6d6fe40

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_EvalConeChartMonomialNeZero

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
open MvPolynomial
noncomputable section
variable {ι : Type} [Fintype ι] [DecidableEq ι] {n : ι → ℕ}
open GroundTheory.Heights₂.Heights.BoundedMonomials
omit [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights.BoundedMonomials
theorem _root_.solution (f : MvPolynomial (Coord n) ℤ) :
    Continuous fun z : Cone n ℂ ↦ evalCone z f := by
  have h : (fun z : Cone n ℂ ↦ evalCone z f) =
      fun z ↦ eval (fun v : Coord n ↦ z v.1 v.2) (map (Int.castRingHom ℂ) f) := by
    funext z
    rw [eval_map]
    rfl
  rw [h]
  exact (continuous_eval _).comp
    (continuous_pi fun v ↦ (continuous_apply v.2).comp (continuous_apply v.1))
end GroundTheory.Heights₂.Heights.BoundedMonomials
