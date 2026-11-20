-- Prove2me | solution 1 for QEC.Coding.BDL26LocalBackgroundComparisonGeometry.native_response_obstruction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T15:42:00.915115+00:00
-- url     : https://prove2.me/submissions/c93dac27-1650-437c-8fcb-cc56bcbc8451

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonDepth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_LocalBackgroundComparisonGeometry
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26LocalBackgroundComparisonDepth_fixed_scale_no_bounded_response
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_supported_word_weight_le


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
theorem _root_.solution {L : ℝ} (p : GeometricParameters L)
    (large : 33 ≤ (perturbationOddScale p).ell) (R : ℝ) :
    ∃ (g : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))
      (q : Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R))),
      ballBudget p.t R < HammingWeight g ∧ g ≠ 0 ∧
      canonicalBasisWord (F:=BDL26Field) q ≠
        (0 : W (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) ∧
      BDL26AllDepthBottomComparisonStability.residual (perturbationOddScale p) (budgetDepth (ballBudget p.t R))
        (perturbTop (perturbationOddScale p) (budgetDepth (ballBudget p.t R))
          (BDL26NonzeroBackgroundComparisonStability.zeroInput (perturbationOddScale p) (budgetDepth (ballBudget p.t R))) g)
        (canonicalBasisWord (F:=BDL26Field) q) ∉
          boundaries (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) ∧
      ∀ (z : BDL26NativeFiniteComposition.Experiment p (responseLevel p.t R)),
        z ∈ BDL26NativeFiniteComposition.finiteSuccess p (responseLevel p.t R) →
        ∀ (center : Space) (A : Finset (Q (perturbationOddScale p) (budgetDepth (ballBudget p.t R)))),
          (∀ u ∈ hammingSupport (backgroundRestriction (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g A),
            dist (BDL26NativeFiniteComposition.history p (responseLevel p.t R) z
              (Fin.last (responseLevel p.t R)) (.q u)) center ≤ R) →
          ChangesDefect (perturbationOddScale p) (budgetDepth (ballBudget p.t R)) g q A := by
  let S := perturbationOddScale p
  let B := ballBudget p.t R
  let n := budgetDepth B
  obtain ⟨P,q,hP,hq,hn,heavy,nonzero,flip,bad,exclude⟩ := fixed_scale_no_bounded_response S large B
  let g := backgroundRestriction S n (BDL26HistoryLogicalResidual.logicalError S n) P
  refine ⟨g,q,heavy,nonzero,flip,bad,?_⟩
  intro z success center A inside
  have geometry := BDL26NativeFiniteComposition.finiteSuccess_geometry p (responseLevel p.t R) success
    (Fin.last (responseLevel p.t R))
  have small : HammingWeight (backgroundRestriction S n g A) ≤ B :=
    supported_word_weight_le S (n+2) _ geometry R center (backgroundRestriction S n g A) inside
  exact exclude A small
end QEC.Coding.BDL26LocalBackgroundComparisonGeometry
