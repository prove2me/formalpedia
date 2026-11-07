-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.planeVExpr_eval
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:20:59.583434+00:00
-- url     : https://prove2.me/submissions/69d4dbd6-161f-4edd-a357-806b3f3e7694

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_dotExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_subExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_determinantExpr_eval
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
theorem _root_.solution (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    planeVExpr.eval a z ρ = planeV (a 1-a 0) (a 2-a 0) (z-a 0) := by
  have hb := subExpr_eval (vertexExpr 1) (vertexExpr 0) a z ρ (a 1) (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hc := subExpr_eval (vertexExpr 2) (vertexExpr 0) a z ρ (a 2) (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hd := subExpr_eval centerExpr (vertexExpr 0) a z ρ z (a 0)
    (fun _ => rfl) (fun _ => rfl)
  have hbb := dotExpr_eval _ _ a z ρ _ _ hb hb
  have hdb := dotExpr_eval _ _ a z ρ _ _ hd hb
  have hdc := dotExpr_eval _ _ a z ρ _ _ hd hc
  have hbc := dotExpr_eval _ _ a z ρ _ _ hb hc
  simp only [planeVExpr,RealExpr.eval,hbb,hdb,hdc,hbc,determinantExpr_eval,
    real_inner_self_eq_norm_sq,planeV]
end QEC.Coding.BDL26RandomPerturbation
