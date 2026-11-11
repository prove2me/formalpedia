-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_eligiblePairQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:26:31.309548+00:00
-- url     : https://prove2.me/submissions/98af756e-db48-49a0-a630-53560cb6c0e6

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_anchorCloseQuery

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation) (r : ℝ)
    (a b : Triangle P) :
    Measurable (fun J : Vertex P → Space => eligiblePairQuery P J r a b) := by
  exact (measurable_of_countable (fun t : Bool × ℕ =>
    ((colorMatchQuery P a b).1 && t.1, (colorMatchQuery P a b).2 + t.2 + 1))).comp
    (measurable_anchorCloseQuery P r a b)
end QEC.Coding.BDL26RandomPerturbation
