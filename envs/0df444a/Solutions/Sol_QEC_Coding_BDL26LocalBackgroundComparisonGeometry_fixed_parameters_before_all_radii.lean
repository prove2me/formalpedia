-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonGeometry.fixed_parameters_before_all_radii
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:58:30.58018+00:00
-- url     : https://prove2.me/submissions/4071a87c-1119-44c9-83b7-43d199e66421

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonGeometry
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonGeometry_native_response_obstruction_ae
import Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_large_parameters_exist


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26LocalBackgroundComparisonGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26HistorySyndromeSensitivity BDL26HistoryErrorTelescoping
open BDL26LocalBackgroundComparisonResponse BDL26LocalBackgroundComparisonDepth
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26LocalBackgroundComparisonGeometry
theorem _root_.solution (L : ℝ) :
    ∃ p : GeometricParameters L, 33 ≤ (perturbationOddScale p).ell ∧
      ∀ R : ℝ,
    ∃ (g : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))
      (q : Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R))),
      g ≠ 0 ∧ canonicalBasisWord (F:=BDL26Field) q ≠
        (0 : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) ∧
      ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (responseLevel p.t R),
        ∀ (center : Space) (A : Finset (Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))),
          (∀ u ∈ hammingSupport (backgroundRestriction (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g A),
            dist (BDL26NativeFiniteComposition.history p (responseLevel p.t R) z
              (Fin.last (responseLevel p.t R)) (.q u)) center ≤ R) →
          ChangesDefect (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g q A := by
  obtain ⟨p,large⟩ := large_parameters_exist L
  exact ⟨p,large,fun R => native_response_obstruction_ae p large R⟩
end QEC.Coding.BDL26LocalBackgroundComparisonGeometry
