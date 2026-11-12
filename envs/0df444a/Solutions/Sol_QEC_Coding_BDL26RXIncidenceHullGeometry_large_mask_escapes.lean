-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGeometry.large_mask_escapes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T12:40:50.209264+00:00
-- url     : https://prove2.me/submissions/7043356d-00e9-4caa-ae2e-641f145bfa7d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
import Theorems.Thm_QEC_Coding_BDL26QubitBallBounds_mask_card_le


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RXIncidenceHullGeometry
open Classical MeasureTheory ProbabilityTheory
open MultiscaleDecoder BDL26IndexedDecoder BDL26FiniteTannerSquare BDL26DecodingGraph
open BDL26RandomPerturbation BDL26RandomPhysicalLocality BDL26QubitBallBounds
open BDL26RXDifferentialMasks BDL26RXIncidenceHullRetainedGrowth
open QEC.Coding.ProbabilisticConstruction.SphericalCap
namespace QEC.Coding.BDL26RXIncidenceHullGeometry
theorem _root_.solution (S : OddScale) (m : Nat)
    (J : Vertex (state S m).presentation → Space) {t : ℝ}
    (geometry : PhysicalGeometry S m J t) (R : ℝ)
    (A : Finset (state S m).presentation.Q) (heavy : ballBudget t R < A.card)
    (center : Space) : ∃ q ∈ A, R < dist (J (.q q)) center := by
  by_contra none
  have inside : ∀ q ∈ A, dist (J (.q q)) center ≤ R := by
    intro q hq
    exact le_of_not_gt (fun beyond => none ⟨q,hq,beyond⟩)
  have bound := mask_card_le S m J geometry R center A inside
  omega
end QEC.Coding.BDL26RXIncidenceHullGeometry
