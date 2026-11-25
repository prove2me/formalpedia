-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_FiniteCoverPuncturedPolydisc_mem_strip_of_exp_c648e578c497
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:56:44.706834+00:00
-- url     : https://prove2.me/submissions/00994ec0-6d46-4836-8195-fda9e37bbc66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StFiniteCoverPuncturedPolydisc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFiniteCoverPuncturedPolydisc

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
open Filter Topology Complex
open scoped Real
noncomputable section
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc
variable {e : ℕ}
variable {c : Fin (e + 1) → ℂ} {r : ℝ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc
theorem _root_.solution (hc : c 0 = 0) {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) {t : Fin (e + 1) → ℂ}
    (ht : t ∈ Metric.ball c ρ) {w : ℂ} (hw : exp w = t 0) {k : ℕ} (hk : 1 ≤ k) :
    Function.update t 0 (k * w) ∈ strip c ρ := by
  have ht0 : t 0 ≠ 0 := hw ▸ exp_ne_zero w
  have hnorm : ‖t 0‖ < ρ := by
    have := (dist_le_pi_dist t c 0).trans_lt ht
    simpa [hc] using this
  have hre : w.re = Real.log ‖t 0‖ := by rw [← hw, norm_exp, Real.log_exp]
  have hlog : Real.log ‖t 0‖ < Real.log ρ := Real.log_lt_log (norm_pos_iff.2 ht0) hnorm
  have hlogρ : Real.log ρ ≤ 0 := Real.log_nonpos hρ0.le hρ1
  refine ⟨?_, fun i hi => ?_⟩
  · simp only [Function.update_self, mul_re, natCast_re, natCast_im, zero_mul, sub_zero, hre]
    have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
    nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.2 hk') (hlog.trans_le hlogρ).le]
  · rw [Function.update_of_ne hi]
    exact (dist_le_pi_dist t c i).trans_lt ht
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.FiniteCoverPuncturedPolydisc
