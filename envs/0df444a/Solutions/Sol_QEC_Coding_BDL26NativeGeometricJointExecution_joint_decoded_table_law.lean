-- Prove2me | solution 1 for QEC.Coding.BDL26NativeGeometricJointExecution.joint_decoded_table_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T10:07:28.863109+00:00
-- url     : https://prove2.me/submissions/bb402d9b-3ac2-4c5c-b98f-a0304b7fd52a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricExecutionCost
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_NativeGeometricJointExecution
import Theorems.Thm_QEC_Coding_BDL26NativeGeometricExecution_decoded_table_law
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_VariableRelabeling_measurable_decodeTable


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26NativeGeometricJointExecution
open BDL26FiniteAlternatingCore BDL26FiniteTannerSquare BDL26BoundedValence
open BDL26ReplacementEmbedding BDL26TannerLocalRegularity
open BDL26RandomPerturbation BDL26KeyedGeometric BDL26KeyedGeometricExecution
open BDL26NativeKeyExecutionBridge BDL26NativeGeometricExecution
open BDL26NativeGeometricScanCost BDL26NativeGeometricExecutionCost
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
open scoped Classical BigOperators ENNReal
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
attribute [local instance] QEC.Coding.BDL26NativeGeometricJointExecution.labelListMeasurable QEC.Coding.BDL26NativeGeometricJointExecution.labelListSingleton
namespace QEC.Coding.BDL26NativeGeometricJointExecution
theorem _root_.solution (S : OddScale) (n : ℕ) {L : ℝ}
    (p : GeometricParameters L) (ν : Measure (Input S n)) [IsProbabilityMeasure ν] :
    (ν.prod (nativeTableMeasure S n p)).map
        (fun z : JointInput S n => (z.1,decodedTable S n z.2)) =
      ν.prod (tableMeasure (Presentation S n) p) := by
  have hd : Measurable (decodedTable S n) :=
    Resampling.VariableRelabeling.measurable_decodeTable (SR.decode S n)
  have hm : Measurable (fun z : JointInput S n => (z.1,decodedTable S n z.2)) :=
    measurable_fst.prodMk (hd.comp measurable_snd)
  ext s hs
  rw [Measure.map_apply hm hs,Measure.prod_apply (hm hs),Measure.prod_apply hs]
  apply lintegral_congr
  intro J
  rw [← decoded_table_law S n p,Measure.map_apply hd
    ((measurable_const.prodMk measurable_id :
      Measurable (fun T : OriginalTable S n => (J,T))) hs)]
  rfl
end QEC.Coding.BDL26NativeGeometricJointExecution
