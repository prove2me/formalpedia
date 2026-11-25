-- Prove2me | solution 1 for ReciprocityTheory.L2DbarEstimates.leviV_log_sum_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T14:35:06.969791+00:00
-- url     : https://prove2.me/submissions/8f5191a2-9c4e-4657-985e-bb3a7abc34d3

import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_EventuallyDifferentiableAtOfContDiffAt
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_LeviForms_OfRealNormSqSumMul
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviChain
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_normSq_sum_le_of_le
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_wd_ofReal_sum
import Theorems.Thm_ReciprocityTheory_L2DbarEstimates_leviV_ofReal_sum

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex ComplexConjugate Filter Topology
open ReciprocityTheory ReciprocityTheory.L2DbarEstimates
variable {n : ℕ}
namespace ReciprocityTheory.L2DbarEstimates
theorem _root_.solution {m : ℕ} {u : Fin m → V n → ℝ} {x : V n}
    (hu : ∀ i, ContDiffAt ℝ 2 (u i) x) (hl : ∀ i, LogPshAt n (u i) x) (hpos : 0 < ∑ i, u i x)
    (ξ : Fin n → ℂ) : 0 ≤ (leviV n (fun y => ((Real.log (∑ i, u i y) : ℝ) : ℂ)) x ξ).re := by
  have hS : ContDiffAt ℝ 2 (fun y => ∑ i, u i y) x := ContDiffAt.sum fun i _ => hu i
  have hlog : ContDiffAt ℝ 2 Real.log (∑ i, u i x) := Real.contDiffAt_log.2 hpos.ne'
  have hc := leviChain n Real.log (fun y => ∑ i, u i y) x ξ hS hlog
  have hd1 : deriv Real.log (∑ i, u i x) = (∑ i, u i x)⁻¹ := by rw [Real.deriv_log']
  have hd2 : deriv (deriv Real.log) (∑ i, u i x) = -((∑ i, u i x) ^ 2)⁻¹ := by
    rw [Real.deriv_log']; exact deriv_inv
  rw [hc, hd1, hd2, leviV_ofReal_sum hu]
  have hw : ∀ j, wd n j (fun y => ((∑ i, u i y : ℝ) : ℂ)) x = ∑ i, wd n j (fun y => (u i y : ℂ)) x :=
    fun j => wd_ofReal_sum fun i => (hu i).differentiableAt (by simp)
  simp only [hw, Finset.sum_mul]
  rw [Finset.sum_comm]
  simp only [add_re, re_ofReal_mul, ofReal_re, re_sum]
  set S := ∑ i, u i x
  have key := normSq_sum_le_of_le (fun i => ∑ j, wd n j (fun y => (u i y : ℂ)) x * ξ j) (fun i => u i x)
    (fun i => (leviV n (fun y => (u i y : ℂ)) x ξ).re) (fun i => (hl i).1)
    (fun i => ((hl i).2 ξ).1) (fun i => ((hl i).2 ξ).2)
  set N := Complex.normSq (∑ i, ∑ j, wd n j (fun y => (u i y : ℂ)) x * ξ j)
  set T := ∑ i, (leviV n (fun y => (u i y : ℂ)) x ξ).re
  have hid : S⁻¹ * T + -(S ^ 2)⁻¹ * N = (S * T - N) / S ^ 2 := by field_simp; ring
  rw [hid]
  exact div_nonneg (by linarith) (by positivity)
end ReciprocityTheory.L2DbarEstimates
