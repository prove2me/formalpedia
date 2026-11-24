-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Inter_ptsIntegral_add_of_dimOne_cd9bf8d25634
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T03:57:36.287479+00:00
-- url     : https://prove2.me/submissions/9987fd69-7a8e-4134-8ed4-f4fbb3154229

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_MultihomogeneousIdeals_MemDivSuppOfDivCycleNeZero
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterDivSupp
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_StatementsArith
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsMultiHomogTwoXc
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_MultAtHorizontalEqZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_NotIsHorizontalOfDimOne

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Inter
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2
noncomputable section
variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.Inter
theorem _root_.solution (hFF : FibreFiniteStatement) {P : Ideal (MRing ι)}
    (hP : IsArithVar P 1) (φ : Fin 0 → ((Σ k, ι k) → ℂ) → ℝ) {g g₁ g₂ : ((Σ k, ι k) → ℂ) → ℝ}
    (h : ∀ z ∈ mcPts P, g z = g₁ z + g₂ z) :
    ptsIntegral P φ g = ptsIntegral P φ g₁ + ptsIntegral P φ g₂ := by
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    rw [MeasureTheory.integral_unique, MeasureTheory.integral_unique, MeasureTheory.integral_unique,
      ← smul_add]
    congr 1
    have hfin : ∀ y, (fibre P hΨ.choose y).Finite := hFF K ι P 0 hΨ.choose hP hΨ.choose_spec
    refine Eq.trans ?_ (finsum_mem_add_distrib' ((hfin _).subset Set.inter_subset_left)
      ((hfin _).subset Set.inter_subset_left))
    refine finsum_mem_congr rfl fun w _ => ?_
    unfold sheetDensity
    split_ifs with hγ
    · have hz : ∀ y : Fin 0 → ℂ, hγ.choose y ∈ mcPts P := fun y =>
        (Subsingleton.elim _ y) ▸ hγ.choose_spec.2.self_of_nhds.2.1
      rw [h _ (hz _), add_mul]
    · simp
  · simp
end GroundTheory.Heights₂.Heights.Inter
