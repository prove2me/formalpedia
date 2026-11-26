-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.finiteThetaSum_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:56:36.905797+00:00
-- url     : https://prove2.me/submissions/787557ac-b55c-4aad-8b64-cbb8af7c0719

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.ModularForms.JacobiTheta.TwoVariable
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_pos
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_inv_lt_eulerC
import Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_summable
import Theorems.Thm_SharpIntermediateSubgroupBounds_shiftedTheta_le

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p L : ℝ} (hp : 2 ≤ p) (hL : 0 ≤ L) :
    finiteThetaSum p L <
      sharpConstant p * Real.exp (Real.log p * L ^ 2 / 4) := by
  have hp1 : 1 < p := by linarith
  have hlog : 0 < Real.log p := Real.log_pos hp1
  let N := Nat.floor L + 1
  let center : ℝ := L / 2
  let g : ℤ → ℝ := fun z ↦ Real.exp (-Real.log p * ((z : ℝ) - center) ^ 2)
  have hg : Summable g := shiftedTheta_summable hp1
  have hfirst : finiteThetaSum p L <
      eulerC p * ∑ r ∈ Finset.range N,
        Real.exp (Real.log p * (r : ℝ) * (L - r)) := by
    unfold finiteThetaSum
    simp only [N]
    rw [Finset.mul_sum]
    refine Finset.sum_lt_sum (fun r hr ↦ ?_) ?_
    · exact mul_le_mul_of_nonneg_right (gammaR_inv_lt_eulerC hp r).le
        (Real.exp_nonneg _)
    · refine ⟨0, by simp, ?_⟩
      exact mul_lt_mul_of_pos_right (gammaR_inv_lt_eulerC hp 0) (Real.exp_pos _)
  have hcomplete :
      (∑ r ∈ Finset.range N,
        Real.exp (Real.log p * (r : ℝ) * (L - r))) =
        Real.exp (Real.log p * L ^ 2 / 4) *
          ∑ r ∈ Finset.range N, g (r : ℤ) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Real.exp_add]
    congr 1
    simp only [g, center, Int.cast_natCast]
    ring
  have hfinite_gauss : (∑ r ∈ Finset.range N, g (r : ℤ)) ≤ ∑' z : ℤ, g z := by
    let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
    let s : Finset ℤ := (Finset.range N).map emb
    have hs : (∑ r ∈ Finset.range N, g (r : ℤ)) = ∑ z ∈ s, g z := by
      simp [s, emb]
    rw [hs]
    exact hg.sum_le_tsum s (fun z hz ↦ (Real.exp_pos _).le)
  have htheta : (∑' z : ℤ, g z) ≤ gaussianTheta p := by
    simpa [g, center, shiftedTheta] using shiftedTheta_le (p := p) (x := center) hp1
  calc
    finiteThetaSum p L
        < eulerC p * ∑ r ∈ Finset.range N,
            Real.exp (Real.log p * (r : ℝ) * (L - r)) := hfirst
    _ = eulerC p * (Real.exp (Real.log p * L ^ 2 / 4) *
          ∑ r ∈ Finset.range N, g (r : ℤ)) := by rw [hcomplete]
    _ ≤ eulerC p * (Real.exp (Real.log p * L ^ 2 / 4) * gaussianTheta p) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hfinite_gauss.trans htheta) (Real.exp_nonneg _))
        (eulerC_pos hp).le
    _ = sharpConstant p * Real.exp (Real.log p * L ^ 2 / 4) := by
      simp [sharpConstant]
      ring
end SharpIntermediateSubgroupBounds
