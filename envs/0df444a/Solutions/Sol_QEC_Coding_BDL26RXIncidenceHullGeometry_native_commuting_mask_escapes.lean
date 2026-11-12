-- Prove2me | solution 1 for QEC.Coding.BDL26RXIncidenceHullGeometry.native_commuting_mask_escapes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T13:20:24.886907+00:00
-- url     : https://prove2.me/submissions/d3f4dca2-385f-4d39-ae6c-641689ee2ca2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_QubitBallBounds
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeFiniteComposition
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullRetainedGrowth
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_OwnerIncidenceMasks_RXIncidenceHullGeometry
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_hullStep_even
import Theorems.Thm_QEC_Coding_BDL26RXIncidenceHullGeometry_native_singleton_escapes
import Theorems.Thm_QEC_Coding_BDL26RXDifferentialMasks_incidenceHull_le_every_commuting_pair


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
    (A : Finset (state (perturbationOddScale p) (hullLevel (ballBudget p.t R))).presentation.Q)
    (B : Finset (FamilyZ (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
      (hullStep (ballBudget p.t R)).succ))
    (hseed : seed (perturbationOddScale p) (hullLevel (ballBudget p.t R)) ⊆ A)
    (commutes : ∀ w, maskWord B
      (nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1) (hullStep (ballBudget p.t R)) w) =
      nativeDifferential (perturbationOddScale p) (hullLevel (ballBudget p.t R)+1)
        (hullStep (ballBudget p.t R)) (maskWord A w)) (center : Space) :
    ∃ q ∈ A, R < dist
      (BDL26NativeFiniteComposition.history p (hullLevel (ballBudget p.t R)+1) z
        ⟨hullLevel (ballBudget p.t R),by omega⟩ (.q q)) center := by
  obtain ⟨q,hq,outside⟩ := native_singleton_escapes p R success center
  have contains := (incidenceHull_le_every_commuting_pair (perturbationOddScale p)
    (hullLevel (ballBudget p.t R)+1) (hullStep (ballBudget p.t R)) (hullStep_even _) _ A B hseed commutes).1
  exact ⟨q,contains hq,outside⟩
end QEC.Coding.BDL26RXIncidenceHullGeometry
