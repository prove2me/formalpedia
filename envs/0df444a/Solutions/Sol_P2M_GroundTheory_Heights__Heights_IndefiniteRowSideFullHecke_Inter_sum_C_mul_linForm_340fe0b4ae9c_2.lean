-- Prove2me | solution 2 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_sum_C_mul_linForm_340fe0b4ae9c
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T04:34:42.421863+00:00
-- url     : https://prove2.me/submissions/c058812f-c07b-4bb3-bf4f-c5d6b0c3870b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StProjBundleFibre
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermOfIsPullHermInl
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_PProjBundleFibre

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4
variable {Φ : Type} [Field Φ] {σ : Type} [Fintype σ] {n : ℕ}
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
theorem _root_.solution {τ ρ : Type} [Fintype τ] [Fintype ρ] (c : ρ → Φ) (ν : ρ → τ → Φ) :
    ∑ a, C (c a) * ∑ q, C (ν a q) * (X q : MvPolynomial τ Φ) = ∑ q, C (∑ a, c a * ν a q) * X q := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [map_mul, mul_assoc]
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
