-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.StateRowsRep_rows
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T00:05:54.970308+00:00
-- url     : https://prove2.me/submissions/14af1816-34e7-4c6e-8ca9-4753a0ef6673

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open BDL26FiniteTannerSquare
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped ENNReal
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListMeasurable
attribute [local instance] QEC.Coding.BDL26RandomPerturbation.countedLabelListSingleton
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation)
    (T : Table (X := fun _ : Vertex P => Space)) (c : Counters (Vertex P))
    (R : StateRows P) (hR : StateRowsRep P T c R) :
    R = (vertexInputList P).map (fun v => (v, c v, T (v, c v))) := by
  have he : R.map id = R.map (fun row => (row.1, c row.1, T (row.1, c row.1))) := by
    apply List.map_congr_left
    intro row hr
    exact Prod.ext rfl (hR.2 row hr)
  rw [List.map_id] at he
  calc
    R = R.map (fun row => (row.1, c row.1, T (row.1, c row.1))) := he
    _ = (R.map Prod.fst).map (fun v => (v, c v, T (v, c v))) := by
      rw [List.map_map]
      rfl
    _ = _ := by rw [hR.1]
end QEC.Coding.BDL26RandomPerturbation
