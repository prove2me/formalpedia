-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_analyticAt_evalCone_comp_5cc3e96f85a5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:45.162802+00:00
-- url     : https://prove2.me/submissions/2e766ad3-2c0d-440e-b1da-bd2961b98f8d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_AnalyticAtEvalConeComp

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {ι : Type} [Fintype ι] {n : ι → ℕ} {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] (z : E → Cone n ℂ) (u₀ : E) (hz : ∀ k i, AnalyticAt ℂ (fun u ↦ z u k i) u₀)
    (f : MvPolynomial (Coord n) ℤ) : AnalyticAt ℂ (fun u ↦ evalCone (z u) f) u₀ := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    have h : (fun u ↦ evalCone (z u) (C a)) = fun _ ↦ ((a : ℤ) : ℂ) := by
      funext u; rw [evalCone, eval₂_C]; simp
    rw [h]; exact analyticAt_const
  | add p q hp hq =>
    have h : (fun u ↦ evalCone (z u) (p + q)) = fun u ↦ evalCone (z u) p + evalCone (z u) q := by
      funext u; simp [evalCone]
    rw [h]; exact hp.add hq
  | mul_X p v hp =>
    have h : (fun u ↦ evalCone (z u) (p * X v)) = fun u ↦ evalCone (z u) p * z u v.1 v.2 := by
      funext u; simp [evalCone]
    rw [h]; exact hp.mul (hz v.1 v.2)
end GroundTheory.Heights₂.Heights
