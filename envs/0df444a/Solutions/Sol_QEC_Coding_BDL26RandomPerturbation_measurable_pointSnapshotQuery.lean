-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_pointSnapshotQuery
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-10T23:16:49.509045+00:00
-- url     : https://prove2.me/submissions/67e9f2c7-2f4c-421c-9cee-3bc8f8449fbe

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_pointSnapshotQuery_cost
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_pointSnapshotQuery_value
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
theorem _root_.solution {Ω : Type*} [MeasurableSpace Ω]
    (lambda : ℝ) (a b : Ω → Space) (ha : Measurable a) (hb : Measurable b) :
    Measurable (fun w => pointSnapshotQuery lambda (a w) (b w)) := by
  have he : (fun w => pointSnapshotQuery lambda (a w) (b w)) =
      (fun w => (lambda • ((1/2 : ℝ) • a w) + b w, (24 : ℕ))) := by
    funext w
    exact Prod.ext (pointSnapshotQuery_value lambda (a w) (b w))
      (pointSnapshotQuery_cost lambda (a w) (b w))
  rw [he]
  exact (((ha.const_smul (1/2 : ℝ)).const_smul lambda).add hb).prodMk measurable_const
end QEC.Coding.BDL26RandomPerturbation
