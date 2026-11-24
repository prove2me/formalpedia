-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_Inter_rhsR_equiv_ab54d4a8ce7e
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T00:16:01.618099+00:00
-- url     : https://prove2.me/submissions/33385939-10a8-4eda-8caf-384ccefe51a4

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_IsSmoothHermFubiniStudyO1
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Intersections_ImportsExtraBis

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
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo
variable {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)]
namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
namespace rhsR
theorem _root_.solution (I : Family ι) (P : Ideal (MRing ι)) {n : ℕ} (L : Fin n → HermLine ι)
    (A : HermLine ι) (s : MRing ι) : rhsR I P L A s = recR I P L A s := by
  classical
  unfold rhsR recR horizPart vertPart intPart arInt
  rw [finsum_mem_eq_finite_toFinset_sum _ (divSupp_finite P s), Finset.sum_filter, Finset.sum_filter,
    ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun W _ => ?_
  by_cases h : IsHorizontal W
  · simp [h]
  · simp only [h, if_false, if_true, not_false_eq_true, zero_add, mul_assoc]
    rfl
end rhsR
end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
