-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometricExecution.result_support_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T08:45:25.723053+00:00
-- url     : https://prove2.me/submissions/70542a8b-1023-46e6-84e7-1a6a7b090774

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_assignment_cap_support
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_capCutoff_bounds


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26KeyedGeometricExecution
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding
open BDL26RandomPerturbation BDL26KeyedGeometric
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
namespace QEC.Coding.BDL26KeyedGeometricExecution
theorem _root_.solution (P : TannerSquarePresentation) (k : Triangle P → ℕ)
    (hk : Function.Injective k) (J : Vertex P → Space) {L : ℝ}
    (p : GeometricParameters L) :
    ∀ᵐ T ∂tableMeasure P p, result P k hk J p T ∈ geometricSupport P p := by
  letI (v : Vertex P) := vertexLaw_probability P
    ((6*p.m : ℕ)*(p.lambda : ℝ)) (capCutoff_bounds p.m_two).2 v
  have hm : 0 < 6*p.m := by have h := p.m_two; omega
  have hmR : (0 : ℝ) < (6*p.m : ℕ) := by exact_mod_cast hm
  have hlR : (0 : ℝ) < p.lambda := by
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one p.lambda_one)
  filter_upwards [assignment_cap_support P (mul_pos hmR hlR)
    (capCutoff_bounds p.m_two).2] with T hT
  exact hT _
end QEC.Coding.BDL26KeyedGeometricExecution
