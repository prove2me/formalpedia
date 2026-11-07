-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangleQueryProgram_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:47:38.856676+00:00
-- url     : https://prove2.me/submissions/abc6873c-ec90-48d9-8b01-8636bb70bf92

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_segmentExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_determinantExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_planeUExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_planeVExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_planeExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_distanceTest_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleBallTest_iff
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_fst
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_axialEquiv_snd_apply
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_SphericalCap_barycenterMap_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_fst
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.axialEquiv_snd_apply
attribute [local simp] QEC.Coding.ProbabilisticConstruction.SphericalCap.barycenterMap_apply


attribute [local simp] QEC.Coding.BDL26RandomPerturbation.vertexExpr_eval
attribute [local simp] QEC.Coding.BDL26RandomPerturbation.centerExpr_eval

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped InnerProductSpace BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (a : Fin 3 → Space) (z : Space) {ρ : ℝ}
    (hρ : 0 ≤ ρ) : triangleQueryProgram.eval a z ρ = true ↔
      ∃ y ∈ convexHull ℝ (Set.range a), dist y z ≤ ρ := by
  have hv (i : Fin 3) := distanceTest_eval (vertexExpr i) a z ρ (a i) (fun _ => rfl) hρ
  have hs (i j : Fin 3) := distanceTest_eval (segmentExpr i j) a z ρ
    (segmentPoint (a i) (a j) z) (fun l => segmentExpr_eval i j l a z ρ) hρ
  have hp := distanceTest_eval planeExpr a z ρ (planePoint a z)
    (fun j => planeExpr_eval j a z ρ) hρ
  rw [← triangleBallTest_iff]
  simp only [triangleQueryProgram,RealTest.eval,RealExpr.eval,Bool.and_eq_true,
    Bool.or_eq_true,decide_eq_true_eq,hρ,true_and,determinantExpr_eval,
    planeUExpr_eval,planeVExpr_eval,hv,hs,hp]
  unfold triangleBallTest planeFeasible
  constructor
  · rintro (h | h | h | h | h | h | h)
    · exact Or.inl ⟨0,h⟩
    · exact Or.inl ⟨1,h⟩
    · exact Or.inl ⟨2,h⟩
    · exact Or.inr (Or.inl ⟨0,1,by decide,h⟩)
    · exact Or.inr (Or.inl ⟨0,2,by decide,h⟩)
    · exact Or.inr (Or.inl ⟨1,2,by decide,h⟩)
    · exact Or.inr (Or.inr ⟨⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩,h.2.2.2.2⟩)
  · rintro (⟨i,hi⟩ | ⟨i,j,hij,hd⟩ | ⟨h,hp⟩)
    · fin_cases i <;> aesop
    · fin_cases i <;> fin_cases j <;> norm_num at hij <;> aesop
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        ⟨h.1,h.2.1,h.2.2.1,h.2.2.2,hp⟩)))))
end QEC.Coding.BDL26RandomPerturbation
