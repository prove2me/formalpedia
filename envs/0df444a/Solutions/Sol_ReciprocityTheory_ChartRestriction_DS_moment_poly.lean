-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.moment_poly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T12:23:58.25967+00:00
-- url     : https://prove2.me/submissions/8c0b75f5-43b8-4e41-913e-c1e13b173d96

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_TensorRepresentations_MomentMatch

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {ι κ : Type*} [Fintype ι] [Fintype κ] (b : ι → ℂ) (u : ι → ℂ) (a : κ → ℂ)
    (r : κ → ℂ) (h : ∀ k : ℕ, ∑ i, u i * b i ^ k = ∑ s, r s * a s ^ k) (Q : ℂ[X]) :
    ∑ i, u i * Q.eval (b i) = ∑ s, r s * Q.eval (a s) := by
  simp only [Polynomial.eval_eq_sum_range, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  calc ∑ i, u i * (Q.coeff k * b i ^ k) = Q.coeff k * ∑ i, u i * b i ^ k := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    _ = Q.coeff k * ∑ s, r s * a s ^ k := by rw [h k]
    _ = ∑ s, r s * (Q.coeff k * a s ^ k) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
end ReciprocityTheory.ChartRestriction.DS
