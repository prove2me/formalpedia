-- Prove2me | solution 1 for OnlinePrimalDual.BoundedAllocation.theorem13_1
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T22:32:44.636877+00:00
-- url     : https://prove2.me/submissions/02c67ac7-2158-4ce5-af4f-e9d441d4d5d4

import Mathlib
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_AllocationInstance
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_competitiveRatio
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_packingFeasible
import Definitions.Def_OnlinePrimalDual_BoundedAllocation_packingValue

namespace OnlinePrimalDual.BoundedAllocation

theorem aux_t131_ratio_pos (d : ℕ) (hd : 2 ≤ d) : 0 < competitiveRatio d := by
  unfold competitiveRatio
  have hd' : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h1 : (0 : ℝ) < (d : ℝ) - 1 := by linarith
  have hX : (1 : ℝ) ≤ (1 + 1 / ((d : ℝ) - 1)) ^ (d - 1) := by
    apply one_le_pow₀
    have : 0 ≤ 1 / ((d : ℝ) - 1) := by positivity
    linarith
  have hden : (d : ℝ) ≤ (d : ℝ) * (1 + 1 / ((d : ℝ) - 1)) ^ (d - 1) := by
    have : (0 : ℝ) ≤ d := by linarith
    nlinarith
  have hlt : ((d : ℝ) - 1) / ((d : ℝ) * (1 + 1 / ((d : ℝ) - 1)) ^ (d - 1)) < 1 := by
    rw [div_lt_one (by linarith)]
    linarith
  linarith

end OnlinePrimalDual.BoundedAllocation

open OnlinePrimalDual.BoundedAllocation

theorem solution {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    (inst : AllocationInstance I J) (yAlg : I → J → ℝ) (hyAlg_feasible : packingFeasible inst yAlg)
    (ΔX ΔY : J → ℝ) (hΔY_def : ∀ j, ΔY j = ∑ i ∈ inst.S j, inst.b j * yAlg i j)
    (hinvariant : ∀ j, ΔX j ≤ (1 / competitiveRatio inst.d) * ΔY j)
    (hX_ge : ∀ y'', packingFeasible inst y'' → packingValue inst y'' ≤ ∑ j, ΔX j) :
    ∀ y'' : I → J → ℝ, packingFeasible inst y'' →
      competitiveRatio inst.d * packingValue inst y'' ≤ packingValue inst yAlg := by
  intro y'' hy''
  have hC : 0 < competitiveRatio inst.d := aux_t131_ratio_pos inst.d inst.hd
  have h1 : packingValue inst y'' ≤ ∑ j, ΔX j := hX_ge y'' hy''
  have h2 : ∑ j, ΔX j ≤ ∑ j, (1 / competitiveRatio inst.d) * ΔY j :=
    Finset.sum_le_sum (fun j _ => hinvariant j)
  have h3 : packingValue inst yAlg = ∑ j, ΔY j := by
    unfold packingValue
    exact Finset.sum_congr rfl (fun j _ => (hΔY_def j).symm)
  rw [← Finset.mul_sum] at h2
  have h4 : competitiveRatio inst.d * packingValue inst y'' ≤
      competitiveRatio inst.d * ((1 / competitiveRatio inst.d) * ∑ j, ΔY j) :=
    mul_le_mul_of_nonneg_left (h1.trans h2) hC.le
  rw [← mul_assoc, mul_one_div_cancel hC.ne', one_mul] at h4
  rw [h3]
  exact h4
