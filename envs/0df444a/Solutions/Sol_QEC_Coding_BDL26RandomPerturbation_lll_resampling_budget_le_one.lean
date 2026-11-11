-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.lll_resampling_budget_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T22:48:39.905205+00:00
-- url     : https://prove2.me/submissions/57f42b17-f9ea-4179-8014-4762a71d8a7e

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_InputSize
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ExpectedSteps
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_lllWeight_bounds


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare BDL26BoundedValence BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {I : Type*} (D : ℕ) (i : I) :
    resamplingBudget (fun _ : I => lllWeight D) i ≤ 1 := by
  have hx := lllWeight_bounds D
  unfold resamplingBudget
  apply (div_le_iff₀ (sub_pos.mpr hx.2.2)).mpr
  linarith [hx.2.1]
end QEC.Coding.BDL26RandomPerturbation
