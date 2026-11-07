-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.RealExpr.run_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T10:21:06.45862+00:00
-- url     : https://prove2.me/submissions/cf216d6f-c243-46bb-89f6-17c30ba27d52

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_TriangleDecision
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExactRealProgram
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_vertexExpr_eval
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_centerExpr_eval
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
namespace RealExpr
theorem _root_.solution (e : RealExpr) (a : Fin 3 → Space) (z : Space) (ρ : ℝ) :
    (e.run a z ρ).1 = e.eval a z ρ := by
  induction e <;> simp_all only [RealExpr.run,RealExpr.eval]
  split_ifs with h
  · simp_all
  · rfl
end RealExpr
end QEC.Coding.BDL26RandomPerturbation
