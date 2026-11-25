-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_aeval_div_chart_mem_033f1d97cce8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T05:25:35.41385+00:00
-- url     : https://prove2.me/submissions/03fad85c-d83d-4cfe-9d00-ed206cd49bfe

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightsOfSets_FiniteSupportHeight
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_WeightedHomogeneous_Objects
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ArithmeticHilbertSamuelLowerBound
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_InterSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ArithmeticIntersection_RationalSections_IsRatSectionOn
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightComparison_HeightObjects

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G
open scoped ContDiff
noncomputable section
variable {ι : Type} {n : ι → ℕ}
variable [Fintype ι] [DecidableEq ι]
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution {Ω : Type*} [Field Ω] (y : Coord n → Ω) (c : (k : ι) → Fin (n k + 1))
    (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (e : MvPolynomial (Coord n) ℤ) (δ : ι → ℕ)
    (he : IsWeightedHomogeneous (coordDeg n) e δ) :
    aeval y e * ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹ ∈ Geo.chartRingZ (ι := blockIdx n) y c := by
  classical
  rw [aeval_def, eval₂_eq, Finset.sum_mul]
  refine Subalgebra.sum_mem _ fun m hm ↦ ?_
  have hmδ : ∀ k, ∑ i, m ⟨k, i⟩ = δ k := (geoMultiHomog_iff e δ).mpr he m hm
  have key : (algebraMap ℤ Ω (coeff m e) * ∏ p ∈ m.support, y p ^ m p) * ∏ k, (y ⟨k, c k⟩ ^ δ k)⁻¹ =
      algebraMap ℤ Ω (coeff m e) * ∏ p, (y p / y ⟨p.1, c p.1⟩) ^ m p := by
    rw [mul_assoc]
    congr 1
    rw [Finset.prod_subset (Finset.subset_univ m.support) (fun p _ hp ↦ by
      rw [Finsupp.notMem_support_iff.mp hp, pow_zero])]
    have hden : ∏ p : Coord n, y ⟨p.1, c p.1⟩ ^ m p = ∏ k, y ⟨k, c k⟩ ^ δ k := by
      rw [Fintype.prod_sigma]
      refine Finset.prod_congr rfl fun k _ ↦ ?_
      rw [← hmδ k, ← Finset.prod_pow_eq_pow_sum]
    simp_rw [div_pow]
    rw [Finset.prod_div_distrib, hden, div_eq_mul_inv, Finset.prod_inv_distrib]
  rw [key]
  refine Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.prod_mem _ fun p _ ↦ ?_)
  exact Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_range_self p)) _
end GroundTheory.Heights₂.Heights
