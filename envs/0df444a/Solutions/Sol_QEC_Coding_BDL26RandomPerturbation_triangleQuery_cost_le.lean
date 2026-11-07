-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.triangleQuery_cost_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T14:52:12.991764+00:00
-- url     : https://prove2.me/submissions/127b42ef-c72d-4171-b04d-48ecc56a373c

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_triangleQueryProgram_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealExpr_run_cost_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_RealTest_run_cost_le
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
    (triangleQuery a z ρ).2 ≤ 200000 := by
  have h := triangleQueryProgram.run_cost_le a z ρ
  have hc := triangleQueryProgram_cost_le
  dsimp [triangleQuery]
  omega
end QEC.Coding.BDL26RandomPerturbation
