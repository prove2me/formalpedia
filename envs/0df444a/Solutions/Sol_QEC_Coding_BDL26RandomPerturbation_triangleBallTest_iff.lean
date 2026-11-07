-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangleBallTest_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:46:20.763132+00:00
-- url     : https://prove2.me/submissions/dae8b550-c167-48ac-af95-aa1b7f385473

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SingularTriangle
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_segmentPoint_mem_triangle
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_planePoint_mem_triangle
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_barycenter_affine_coordinates
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_boundary_weights_on_edge
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_positive_weights_stationary
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_segmentPoint_nearest
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_singular_weights_on_edge
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_stationary_weights_plane
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangle_nearest_weights
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open Set
open scoped BigOperators InnerProductSpace
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    triangleBallTest a z ρ ↔ ∃ y ∈ convexHull ℝ (range a), dist y z ≤ ρ := by
  constructor
  · rintro (⟨i,hi⟩ | ⟨i,j,_,hij⟩ | ⟨h,hp⟩)
    · exact ⟨a i,subset_convexHull ℝ _ (mem_range_self i),by simpa [dist_comm] using hi⟩
    · exact ⟨segmentPoint (a i) (a j) z,segmentPoint_mem_triangle a z i j,
        by simpa [dist_comm] using hij⟩
    · exact ⟨planePoint a z,planePoint_mem_triangle a z h,by simpa [dist_comm] using hp⟩
  · rintro ⟨x,hx,hxz⟩
    obtain ⟨w,hmin,hi⟩ := triangle_nearest_weights a z
    have hwρ : dist z (barycenterMap a w) ≤ ρ :=
      (hmin x hx).trans (by simpa [dist_comm] using hxz)
    have hedge : (∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
        barycenterMap a w = a i+t • (a j-a i)) → triangleBallTest a z ρ := by
      rintro ⟨i,j,hij,t,ht0,ht1,he⟩
      right; left
      refine ⟨i,j,hij,?_⟩
      exact (segmentPoint_nearest (a i) (a j) z ht0 ht1).trans (he ▸ hwρ)
    by_cases hzero : ∃ i, w.val i = 0
    · exact hedge (boundary_weights_on_edge a w hzero)
    · by_cases hdet : gramDet (a 1-a 0) (a 2-a 0) = 0
      · exact hedge (singular_weights_on_edge a w hdet)
      · have hpos : ∀ i, 0 < w.val i := fun i =>
          lt_of_le_of_ne (w.property.1 i) (Ne.symm (fun h => hzero ⟨i,h⟩))
        have hstation := positive_weights_stationary a z w hpos hi
        obtain ⟨hu,hv⟩ := stationary_weights_plane a z w hstation hdet
        right; right
        refine ⟨⟨hdet,?_,?_,?_⟩,?_⟩
        · rw [← hu]; exact w.property.1 1
        · rw [← hv]; exact w.property.1 2
        · rw [← hu,← hv]
          have hs := w.property.2
          simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
          change w.val 0+(w.val 1+w.val 2) = 1 at hs
          linarith [w.property.1 0]
        · have he : barycenterMap a w = planePoint a z := by
            rw [barycenter_affine_coordinates,hu,hv]
            rfl
          simpa only [he] using hwρ
end QEC.Coding.BDL26RandomPerturbation
