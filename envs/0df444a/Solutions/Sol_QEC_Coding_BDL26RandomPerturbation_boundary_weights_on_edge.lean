-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.boundary_weights_on_edge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:17.765339+00:00
-- url     : https://prove2.me/submissions/1d4d8905-32fd-4421-9f79-b9a20bcb4883

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GramProjection
import Mathlib.Analysis.Convex.Topology
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleMinimum
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_barycenter_affine_coordinates
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
theorem _root_.solution (a : Fin 3 → Space) (w : stdSimplex ℝ (Fin 3))
    (hw : ∃ i, w.val i = 0) :
    ∃ i j : Fin 3, i < j ∧ ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
      barycenterMap a w = a i+t • (a j-a i) := by
  have hs := w.property.2
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at hs
  change w.val 0+(w.val 1+w.val 2) = 1 at hs
  have h0 := w.property.1 0
  have h1 := w.property.1 1
  have h2 := w.property.1 2
  obtain ⟨i,hi⟩ := hw
  fin_cases i
  · change w.val 0 = 0 at hi
    refine ⟨1,2,by decide,w.val 2,h2,by linarith,?_⟩
    rw [barycenterMap_apply]
    simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero]
    have he : w.val 1 = 1-w.val 2 := by linarith
    change w.val 0 • a 0+(w.val 1 • a 1+w.val 2 • a 2) = _
    rw [hi,he]
    module
  · change w.val 1 = 0 at hi
    refine ⟨0,2,by decide,w.val 2,h2,by linarith,?_⟩
    rw [barycenter_affine_coordinates,hi]
    module
  · change w.val 2 = 0 at hi
    refine ⟨0,1,by decide,w.val 1,h1,by linarith,?_⟩
    rw [barycenter_affine_coordinates,hi]
    module
end QEC.Coding.BDL26RandomPerturbation
