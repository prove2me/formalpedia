-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InvarianceOfDomain_radialPush_mem_sphere_21c7ebc5639d
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T03:27:45.165254+00:00
-- url     : https://prove2.me/submissions/d0dbb37f-f932-446a-91ab-9908e2ec33c7

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
theorem _root_.solution {c y : Fin n → ℝ} {ρ : ℝ} (hy : dist y c < ρ) (hyc : y ≠ c) :
    radialPush c ρ y ∈ sphere c ρ := by
  rw [dist_eq_norm] at hy
  have hpos : 0 < ‖y - c‖ := norm_pos_iff.2 (sub_ne_zero.2 hyc)
  have h1 : 1 ≤ ρ / ‖y - c‖ := (one_le_div hpos).2 hy.le
  rw [mem_sphere, dist_eq_norm, radialPush, max_eq_right h1, add_sub_cancel_left, norm_smul,
    Real.norm_of_nonneg (div_nonneg (hpos.trans hy).le hpos.le), div_mul_cancel₀ ρ hpos.ne']
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.InvarianceOfDomain
