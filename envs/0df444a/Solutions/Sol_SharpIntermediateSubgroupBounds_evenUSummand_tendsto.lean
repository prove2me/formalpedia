-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.evenUSummand_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:58:15.448616+00:00
-- url     : https://prove2.me/submissions/7eb15564-bf55-4fda-8daa-a13c5934b652

import Definitions.Def_SharpIntermediateSubgroupBounds_QBinomial
import Definitions.Def_SharpIntermediateSubgroupBounds_Theta
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Normed.Group.Tannery
import Definitions.Def_SharpIntermediateSubgroupBounds_Gaussian
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaR_inv_tendsto

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators Topology
open Filter Finset Real
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p j : ℕ} (hp : 2 ≤ p) :
    Tendsto (fun a : ℕ ↦ evenUSummand p a j) atTop
      (nhds (evenGaussianLimitSummand p j)) := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  by_cases hj0 : j = 0
  · subst j
    simpa [evenUSummand, evenGaussianLimitSummand, centerMultiplicity] using
      gammaR_inv_tendsto hpR
  · have hplus := (gammaR_inv_tendsto hpR).comp (tendsto_add_atTop_nat j)
    have hminus := (gammaR_inv_tendsto hpR).comp (tendsto_sub_atTop_nat j)
    have hc : Tendsto (fun _ : ℕ ↦ (p : ℝ)⁻¹ ^ (j * j)) atTop
        (nhds ((p : ℝ)⁻¹ ^ (j * j))) := tendsto_const_nhds
    have ht := hc.mul (hplus.add hminus)
    have hlim : (p : ℝ)⁻¹ ^ (j * j) *
        (eulerC (p : ℝ) + eulerC (p : ℝ)) =
          evenGaussianLimitSummand p j := by
      simp only [evenGaussianLimitSummand, centerMultiplicity, if_neg hj0,
        Nat.cast_ofNat]
      ring
    rw [← hlim]
    apply ht.congr'
    filter_upwards [eventually_ge_atTop j] with a ha
    simp [evenUSummand, hj0, ha]
end SharpIntermediateSubgroupBounds
