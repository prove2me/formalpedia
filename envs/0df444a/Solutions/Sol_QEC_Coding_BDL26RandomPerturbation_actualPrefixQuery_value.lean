-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.actualPrefixQuery_value
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-12T00:55:03.09001+00:00
-- url     : https://prove2.me/submissions/ff608c7e-1d7d-498a-8000-adf259dd708d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_StateEventQuery
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EventPreprocessingCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualPrefixQuery_rep
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_StateRowsRep_points


set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal BigOperators
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (J : Vertex P → Space)
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K : ℕ)
    (T : Table (X := fun _ : Vertex P => Space)) (n : ℕ) :
    statePoints (actualPrefixQuery P J r lambda K (eventUniverseQuery P J hr).1 T n).1 =
      assignment T (counters (eventSupport P J r) (eventBad P J r lambda K) T n) :=
  StateRowsRep_points P T _ _ (actualPrefixQuery_rep P J hr lambda K T n)
end QEC.Coding.BDL26RandomPerturbation
