-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.singular_weights_on_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:45:34.829198+00:00
-- url     : https://prove2.me/submissions/774ff4bc-e577-4fc4-9196-0d9506db02ea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SingularTriangle
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_collinear_weights_on_edge
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_barycenter_affine_coordinates
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_gramDet_zero_collinear
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
theorem _root_.solution (a : Fin 3 → Space)
    (w : stdSimplex ℝ (Fin 3)) (hdet : gramDet (a 1-a 0) (a 2-a 0) = 0) :
    ∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      barycenterMap a w = a i+t • (a j-a i) := by
  by_cases hb : a 1-a 0 = 0
  · have hs := w.property.2
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
    change w.val 0+(w.val 1+w.val 2) = 1 at hs
    refine ⟨0,2,by decide,w.val 2,w.property.1 2,?_,?_⟩
    · linarith [w.property.1 0,w.property.1 1]
    · rw [barycenter_affine_coordinates,hb]
      simp
  · exact collinear_weights_on_edge a w _ (gramDet_zero_collinear _ _ hb hdet)
end QEC.Coding.BDL26RandomPerturbation
