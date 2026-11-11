-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.geometric_expected_operations_le_qubits
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:08:04.655561+00:00
-- url     : https://prove2.me/submissions/30ec5670-6cd2-4ace-803c-b08df61ee859

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedOperationCost
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_geometric_expected_operations_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_operation_input_size_le_qubits
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_executionOperationBudget_polynomial
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    (A : TannerSquareAdmissible P) {L : ℝ} (p : GeometricParameters L)
    (hJ : IsBoundedDensityLocalMap P J p.t) (hv : BoundedValence P) :
    letI (v : Vertex P) := vertexLaw_probability P
      ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
    (∫⁻ T, actualExecutionCost P J (by positivity : (0 : ℝ) ≤ anchorRadius p.m)
      p.lambda ((6*p.m+2)*p.lambda) T
      ∂tableLaw (vertexLaw P ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff p.m))) ≤
        (operationConstant ((6*p.m+2)*p.lambda)*(65*Fintype.card P.Q+1)^10 : ℕ) := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have hsize := operation_input_size_le_qubits P A hv
  have hpoly := executionOperationBudget_polynomial (Fintype.card (Triangle P))
    (Fintype.card (Vertex P)) ((6*p.m+2)*p.lambda)
  have hb : executionOperationBudget (Fintype.card (Triangle P)) (Fintype.card (Vertex P))
      ((6*p.m+2)*p.lambda) ≤ operationConstant ((6*p.m+2)*p.lambda)*(65*Fintype.card P.Q+1)^10 := by
    apply hpoly.trans
    apply Nat.mul_le_mul_left
    exact Nat.pow_le_pow_left (by omega) 10
  exact (geometric_expected_operations_le P J p hJ hv).trans ((Nat.cast_le (α := ℝ≥0∞)).mpr hb)
end QEC.Coding.BDL26RandomPerturbation
