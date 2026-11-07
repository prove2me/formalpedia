-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.segmentExpr_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T11:44:22.596902+00:00
-- url     : https://prove2.me/submissions/6f3bab2f-3c3d-4369-a674-30e5bbc2f225

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_dotExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_subExpr_eval
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
theorem _root_.solution (i j l : Fin 3) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (segmentExpr i j l).eval a z ρ = segmentPoint (a i) (a j) z l := by
  have hb := subExpr_eval (vertexExpr j) (vertexExpr i) a z ρ (a j) (a i)
    (fun _ => rfl) (fun _ => rfl)
  have hd := subExpr_eval centerExpr (vertexExpr i) a z ρ z (a i)
    (fun _ => rfl) (fun _ => rfl)
  have hdb := dotExpr_eval _ _ a z ρ _ _ hd hb
  have hbb := dotExpr_eval _ _ a z ρ _ _ hb hb
  rw [real_inner_self_eq_norm_sq] at hbb
  simp only [segmentExpr,addExpr,smulExpr,RealExpr.eval,hdb,hbb,vertexExpr_eval]
  change a i l+max 0 (min 1 (inner ℝ (z-a i) (a j-a i)/‖a j-a i‖^2))*(a j l-a i l) = _
  rfl
end QEC.Coding.BDL26RandomPerturbation
