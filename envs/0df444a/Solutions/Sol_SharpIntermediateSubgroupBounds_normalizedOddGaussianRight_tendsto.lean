-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.normalizedOddGaussianRight_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:04.583397+00:00
-- url     : https://prove2.me/submissions/43a9aa73-6b77-473c-87d5-168591356907

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_inv_tendsto
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_tendsto
import Theorems.Thm_SharpIntermediateSubgroupBounds_normalizedOddGaussianRight_eq
import Theorems.Thm_SharpIntermediateSubgroupBounds_eulerC_pos

section
namespace SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
private theorem tendsto_double_add_one_nat_atTop :
    Tendsto (fun a : ℕ ↦ 2 * a + 1) atTop atTop := by
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
    Tendsto (fun a : ℕ ↦ normalizedOddGaussianRight p a j) atTop
      (nhds (eulerC (p : ℝ) * (p : ℝ)⁻¹ ^ (j * (j + 1)))) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have htwo := (gammaR_tendsto hpR).comp tendsto_double_add_one_nat_atTop
  have hplus₀ := (gammaR_inv_tendsto hpR).comp (tendsto_add_atTop_nat (1 + j))
  have hplus : Tendsto (fun a : ℕ ↦ (gammaR (p : ℝ) (a + 1 + j))⁻¹)
      atTop (nhds (eulerC (p : ℝ))) := by
    change Tendsto (fun a : ℕ ↦ (gammaR (p : ℝ) (a + (1 + j)))⁻¹)
      atTop (nhds (eulerC (p : ℝ))) at hplus₀
    simpa only [Nat.add_assoc] using hplus₀
  have hminus := (gammaR_inv_tendsto hpR).comp (tendsto_sub_atTop_nat j)
  have hc : Tendsto (fun _ : ℕ ↦ (p : ℝ)⁻¹ ^ (j * (j + 1))) atTop
      (nhds ((p : ℝ)⁻¹ ^ (j * (j + 1)))) := tendsto_const_nhds
  have hprod := ((hc.mul htwo).mul hplus).mul hminus
  have htend : Tendsto (fun a : ℕ ↦ normalizedOddGaussianRight p a j) atTop
      (nhds ((p : ℝ)⁻¹ ^ (j * (j + 1)) * (eulerC (p : ℝ))⁻¹ *
        eulerC (p : ℝ) * eulerC (p : ℝ))) := by
    apply hprod.congr'
    filter_upwards [eventually_ge_atTop j] with a ha
    rw [normalizedOddGaussianRight_eq hp ha]
    simp only [Function.comp_apply]
  have hC0 : eulerC (p : ℝ) ≠ 0 := ne_of_gt (eulerC_pos hpR)
  convert htend using 1
  field_simp
end SharpIntermediateSubgroupBounds
