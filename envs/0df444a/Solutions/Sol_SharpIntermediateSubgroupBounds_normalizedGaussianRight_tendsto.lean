-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedGaussianRight_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:01.680278+00:00
-- url     : https://prove2.me/submissions/8fc8e89b-e10a-4466-a5a0-7243d50933bd

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_inv_tendsto
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_tendsto
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedGaussianRight_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_pos

section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private theorem tendsto_double_nat_atTop :
    Tendsto (fun a : ℕ ↦ 2 * a) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with a ha
  omega
end SharpIntermediateSubgroupBounds
end

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ normalizedGaussianRight p a j) atTop
      (nhds (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * j))) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have htwo := (gammaR_tendsto hpR).comp tendsto_double_nat_atTop
  have hplus := (gammaR_inv_tendsto hpR).comp (tendsto_add_atTop_nat j)
  have hminus := (gammaR_inv_tendsto hpR).comp (tendsto_sub_atTop_nat j)
  have hc : Tendsto (fun _ : ℕ ↦ (p : ℝ)⁻¹ ^ (j * j)) atTop
      (nhds ((p : ℝ)⁻¹ ^ (j * j))) := tendsto_const_nhds
  have hprod := ((hc.mul htwo).mul hplus).mul hminus
  have hC0 : eulerC (p : ℝ) ≠ 0 := ne_of_gt (eulerC_pos hpR)
  convert hprod.congr' ?_ using 1
  · field_simp
  · filter_upwards [eventually_ge_atTop j] with a ha
    rw [normalizedGaussianRight_eq hp ha]
    simp only [Function.comp_apply, Nat.add_comm, Nat.mul_comm]
end SharpIntermediateSubgroupBounds
