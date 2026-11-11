-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_actualStepQuery_prefix_cost
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:08:29.251102+00:00
-- url     : https://prove2.me/submissions/18d552f8-d11d-43e8-9514-59e8a34624bf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualStepQuery_cost_labels
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_actualScanQuery_prefix
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_actualPrefixQuery_rep
import Theorems.Thm_QEC_Semantics_QuditSubsystem_ScalarCompression_add


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
    {r : ℝ} (hr : 0 ≤ r) (lambda : ℝ) (K n : ℕ) :
    Measurable (fun w : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
      let events := (eventUniverseQuery P w.1 hr).1
      let R := (actualPrefixQuery P w.1 r lambda K events w.2 n).1
      (actualStepQuery P w.1 r lambda K events w.2 R).2) := by
  have hs := measurable_actualScanQuery_prefix P hr lambda K n
  have hm : Measurable (fun e : Option (MasterEvent P) =>
      match e with | none => 0 | some e => countedMasterRefreshCost P e) :=
    measurable_of_countable _
  convert hs.snd.add (hm.comp hs.fst) using 1
  funext w
  exact actualStepQuery_cost_labels P w.1 r lambda K _ w.2 _
    (actualPrefixQuery_rep P w.1 hr lambda K w.2 n).1
end QEC.Coding.BDL26RandomPerturbation
