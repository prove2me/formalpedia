-- Prove2me | solution 1 for QEC.Coding.BDL26KeyedGeometricExecution.expected_steps_explicit_finite
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T09:26:27.318387+00:00
-- url     : https://prove2.me/submissions/e94cde3e-8391-43a1-b066-7c87666ffbea

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricAvoidance
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_KeyedGeometricExecution
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometricExecution_expected_steps_le
import Theorems.Thm_QEC_Coding_BDL26KeyedGeometric_keyEvent_card_le
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lllWeight_bounds
import Theorems.Thm_QEC_Locality_BGKLSeparatorTree_IsNode_trans


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
    (p : GeometricParameters L) (hJ : IsBoundedDensityLocalMap P J p.t)
    (hv : BoundedValence P) :
    (∫⁻ T, totalSteps (keySupport P k hk J (anchorRadius p.m))
      (keyBad P k hk J (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) T
      ∂tableMeasure P p) ≤
      ENNReal.ofReal ((Fintype.card (Triangle P) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) ∧
    ENNReal.ofReal ((Fintype.card (Triangle P) : ℝ)^4 *
        (lllWeight (dependencyBound p.M)/(1-lllWeight (dependencyBound p.M)))) < ∞ := by
  refine ⟨(expected_steps_le P k hk J p hJ hv).trans ?_, ENNReal.ofReal_lt_top⟩
  apply ENNReal.ofReal_le_ofReal
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast keyEvent_card_le P k hk J (anchorRadius p.m)
  · exact div_nonneg (lllWeight_bounds _).1.le (sub_pos.mpr (lllWeight_bounds _).2.2).le
end QEC.Coding.BDL26KeyedGeometricExecution
