-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangle_nearest_weights
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:03.511221+00:00
-- url     : https://prove2.me/submissions/1b763938-8850-48da-82d2-866905639bab

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_inner_nonpos_distance_le
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_convexHull_range_eq_barycenters


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a : Fin 3 → Space) (z : Space) :
    ∃ w : stdSimplex ℝ (Fin 3),
      (∀ x ∈ convexHull ℝ (range a),
        dist z (barycenterMap a w) ≤ dist z x) ∧
      ∀ i, inner ℝ (z-barycenterMap a w) (a i-barycenterMap a w) ≤ 0 := by
  have hc := convex_convexHull ℝ (range a)
  have hn : (convexHull ℝ (range a)).Nonempty :=
    ⟨a 0,subset_convexHull ℝ _ (mem_range_self 0)⟩
  obtain ⟨y,hy,hmin⟩ := exists_norm_eq_iInf_of_complete_convex hn
    ((Set.finite_range a).isCompact_convexHull ℝ).isComplete hc z
  have hi := (norm_eq_iInf_iff_real_inner_le_zero hc hy).mp hmin
  obtain ⟨w,hw,rfl⟩ := (convexHull_range_eq_barycenters a ▸ hy)
  refine ⟨⟨w,hw⟩,?_,?_⟩
  · intro x hx
    exact inner_nonpos_distance_le _ _ _ (hi x hx)
  · intro i
    exact hi _ (subset_convexHull ℝ _ (mem_range_self i))
end QEC.Coding.BDL26RandomPerturbation
