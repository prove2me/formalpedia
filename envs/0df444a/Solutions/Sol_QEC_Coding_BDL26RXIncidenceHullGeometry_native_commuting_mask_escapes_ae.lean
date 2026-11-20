-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGeometry.native_commuting_mask_escapes_ae
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T09:57:26.628178+00:00
-- url     : https://prove2.me/submissions/accd2ddf-5430-41f9-982a-4bc12b1ff502

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_native_commuting_mask_escapes
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_ae
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_ae


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open BDL26RXDifferentialMasks BDL26RXIncidenceHullRetainedGrowth
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RXIncidenceHullGeometry
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (R : ℝ) :
    ∀ᵐ z ∂BDL26NativeFiniteComposition.experimentLaw p (hullLevel (ballBudget p.t R)+1),
      ∀ (A : Finset (state (perturbationOddScale p) (hullLevel (ballBudget p.t R))).presentation.Q)
    (B : Finset (FamilyZ (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
      (hullStep (ballBudget p.t R)).succ))
    (hseed : seed (perturbationOddScale p) (hullLevel (ballBudget p.t R)) ⊆ A)
    (commutes : ∀ w, maskWord B
      (nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1) (hullStep (ballBudget p.t R)) w) =
      nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
        (hullStep (ballBudget p.t R)) (maskWord A w)) (center : Space),
    ∃ q ∈ A, R < dist
      (BDL26NativeFiniteComposition.history p (hullLevel (ballBudget p.t R)+1) z
        ⟨hullLevel (ballBudget p.t R),by omega⟩ (.q q)) center := by
  filter_upwards [BDL26NativeFiniteComposition.finiteSuccess_ae p (hullLevel (ballBudget p.t R)+1)] with z success
  exact native_commuting_mask_escapes p R success
end QEC.Coding.BDL26RXIncidenceHullGeometry
