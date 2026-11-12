-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGeometry.native_singleton_escapes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:12:28.170371+00:00
-- url     : https://prove2.me/submissions/583a113e-5c5c-45c2-931d-108b905f0904

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_singleton_escapes
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_finiteSuccess_geometry
import Theorems.Thm_QEC_Coding_BDL26NativeFiniteComposition_finiteSuccess_geometry


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open BDL26RXDifferentialMasks BDL26RXIncidenceHullRetainedGrowth
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RXIncidenceHullGeometry
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (R : ℝ)
    {z : BDL26NativeFiniteComposition.Experiment p (hullLevel (ballBudget p.t R)+1)}
    (success : z ∈ BDL26NativeFiniteComposition.finiteSuccess p (hullLevel (ballBudget p.t R)+1))
    (center : Space) :
    ∃ q ∈ incidenceHull (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
      (hullStep (ballBudget p.t R)) (seed (perturbationOddScale p) (hullLevel (ballBudget p.t R))),
      R < dist (BDL26NativeFiniteComposition.history p (hullLevel (ballBudget p.t R)+1) z
        ⟨hullLevel (ballBudget p.t R),by omega⟩ (.q q)) center := by
  exact singleton_escapes (perturbationOddScale p) R _
    (BDL26NativeFiniteComposition.finiteSuccess_geometry p _ success
      ⟨hullLevel (ballBudget p.t R),by omega⟩) center
end QEC.Coding.BDL26RXIncidenceHullGeometry
