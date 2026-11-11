-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_fullCenterQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:09:59.828488+00:00
-- url     : https://prove2.me/submissions/f9ba8e56-b552-4527-bc98-0a65bc54a2c1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_pointSnapshotQuery

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
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω]
    (P : TannerSquarePresentation) (lambda : ℝ) (K : ℕ)
    (a : Option (Triangle P)) (g : Grid K) (J : Ω → Vertex P → Space)
    (hJ : Measurable J) :
    Measurable (fun w => fullCenterQuery P (J w) lambda K a g) := by
  cases a with
  | none => exact measurable_const
  | some t =>
      have hp := measurable_pointSnapshotQuery lambda
        (fun w => J w (.x (P.faceX t.1))) (fun _ : Ω => (gridPointQuery K g).1)
        ((measurable_pi_apply (Vertex.x (P.faceX t.1) : Vertex P)).comp hJ) measurable_const
      have hc := (measurable_of_countable
        (fun n : ℕ => (gridPointQuery K g).2 + n + 2)).comp hp.snd
      exact hp.fst.prodMk hc
end QEC.Coding.BDL26RandomPerturbation
