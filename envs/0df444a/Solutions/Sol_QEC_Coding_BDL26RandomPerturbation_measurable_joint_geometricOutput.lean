-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_joint_geometricOutput
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:42:44.865311+00:00
-- url     : https://prove2.me/submissions/16eff4c3-5442-4e43-bac7-7fbec911be08

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_Execution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_Resampling_ParameterizedExecution
import Definitions.Def_QEC_Coding_ProbabilisticConstruction_SphericalCap_JointTriangleHit
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurableSet_masterBad
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_master_output_original
import Theorems.Thm_QEC_Coding_ProbabilisticConstruction_Resampling_measurable_parameterized_output
import Theorems.Thm_QEC_Locality_NoEdgeBetween_symm


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding
open QEC.Coding.ProbabilisticConstruction
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution (P : TannerSquarePresentation)
    {L : ℝ} (p : GeometricParameters L) : Measurable
      (fun z : (Vertex P → Space) × Table (X := fun _ : Vertex P => Space) =>
        geometricOutput P z.1 p z.2) := by
  have hm := measurable_parameterized_output
      (A := Vertex P → Space) (X := fun _ : Vertex P => Space)
      (masterSupport P)
      (masterBad P (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda))
      (measurableSet_masterBad P _ _ _)
  convert hm using 1
  funext z
  calc
    geometricOutput P z.1 p z.2 =
        output (eventSupport P z.1 (anchorRadius p.m))
          (eventBad P z.1 (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda)) z.2 := by
      unfold geometricOutput
      congr 1 <;> exact Subsingleton.elim _ _
    _ = output (masterSupport P)
        (masterBad P (anchorRadius p.m) p.lambda ((6*p.m+2)*p.lambda) z.1) z.2 :=
      (master_output_original P z.1 _ _ _ z.2).symm
end QEC.Coding.BDL26RandomPerturbation
