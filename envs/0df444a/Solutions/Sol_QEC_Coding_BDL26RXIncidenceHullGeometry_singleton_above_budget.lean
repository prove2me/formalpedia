-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGeometry.singleton_above_budget
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:40:22.157596+00:00
-- url     : https://prove2.me/submissions/43bc5c1b-4446-4193-9792-dbe5f0544cf1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullRetainedGrowth_singleton_hull_card_lower


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open BDL26RXDifferentialMasks BDL26RXIncidenceHullRetainedGrowth
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RXIncidenceHullGeometry
theorem _root_.solution (S : OddScale) (B : Nat) :
    B < (incidenceHull S (hullLevel B+1) (hullStep B) (seed S (hullLevel B))).card := by
  have lower := singleton_hull_card_lower S (hullLevel B+1) (hullStep B)
  have power := (hullLevel B).lt_two_pow_self
  have level : B < hullLevel B := by unfold hullLevel; omega
  change 5*2^(hullLevel B) ≤
    (incidenceHull S (hullLevel B+1) (hullStep B) (seed S (hullLevel B))).card at lower
  omega
end QEC.Coding.BDL26RXIncidenceHullGeometry
