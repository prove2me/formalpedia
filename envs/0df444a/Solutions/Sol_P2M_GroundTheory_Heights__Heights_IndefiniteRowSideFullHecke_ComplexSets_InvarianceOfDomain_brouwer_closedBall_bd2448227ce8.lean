-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_brouwer_closedBall_bd2448227ce8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:27:40.461161+00:00
-- url     : https://prove2.me/submissions/5baedb89-8b41-41e8-900a-708c7bb4716c

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StInvarianceOfDomain
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StBrouwerFixedPoint
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInvarianceOfDomain

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
open Metric Set MeasureTheory
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
theorem _root_.solution (hB : BrouwerFixedPoint.Statement) {a : Fin n → ℝ} {r : ℝ} (hr : 0 < r)
    {h : (Fin n → ℝ) → Fin n → ℝ} (hc : ContinuousOn h (closedBall a r))
    (hm : MapsTo h (closedBall a r) (closedBall a r)) : ∃ x ∈ closedBall a r, h x = x := by
  have haff : MapsTo (fun x : Fin n → ℝ => a + r • x) (closedBall 0 1) (closedBall a r) := by
    intro x hx
    rw [mem_closedBall, dist_zero_right] at hx
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg hr.le]
    nlinarith [norm_nonneg x]
  have hcont : ContinuousOn (fun x : Fin n → ℝ => a + r • x) (closedBall 0 1) :=
    by fun_prop
  have hcomp : ContinuousOn (fun x : Fin n → ℝ => h (a + r • x)) (closedBall 0 1) := hc.comp hcont haff
  obtain ⟨x, hx, hfix⟩ := hB n (fun x => r⁻¹ • (h (a + r • x) - a)) (by fun_prop)
    (by
      intro x hx
      have hy := hm (haff hx)
      rw [mem_closedBall, dist_eq_norm] at hy
      rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_of_nonneg (inv_nonneg.2 hr.le),
        inv_mul_le_iff₀ hr, mul_one]
      exact hy)
  refine ⟨a + r • x, haff hx, ?_⟩
  have h2 : r • (r⁻¹ • (h (a + r • x) - a)) = r • x := by rw [hfix]
  rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at h2
  exact sub_eq_iff_eq_add'.mp h2
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
