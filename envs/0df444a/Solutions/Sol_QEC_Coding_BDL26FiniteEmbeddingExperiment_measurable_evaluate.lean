-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.measurable_evaluate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:01:14.215913+00:00
-- url     : https://prove2.me/submissions/2827712f-2c12-4d0c-ab75-4f555b97666d

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_SeedEmbedding
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteTannerSquare BDL26DecodingGraph BDL26ReplacementEmbedding
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    Measurable (evaluate p n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      change Measurable (fun z : Experiment p n × StageTables p n =>
        physicalSuccessorOutput p n (evaluate p n z.1) z.2)
      have hleft : Measurable (fun z : Experiment p n × StageTables p n =>
          evaluate p n z.1) := ih.comp measurable_fst
      have hright : Measurable (fun z : Experiment p n × StageTables p n => z.2) :=
        measurable_snd
      have hpair : Measurable (fun z : Experiment p n × StageTables p n =>
          (evaluate p n z.1, z.2)) := hleft.prodMk hright
      have hsuccessor : Measurable (fun w : StageMaps p n × StageTables p n =>
          physicalSuccessorOutput p n w.1 w.2) := measurable_joint_physicalSuccessorOutput p n
      exact @Measurable.comp
        (Experiment p n × StageTables p n) (StageMaps p n × StageTables p n) (StageMaps p (n+1))
        inferInstance inferInstance inferInstance
        (fun w : StageMaps p n × StageTables p n => physicalSuccessorOutput p n w.1 w.2)
        (fun z : Experiment p n × StageTables p n => (evaluate p n z.1, z.2))
        hsuccessor hpair
end QEC.Coding.BDL26FiniteEmbeddingExperiment
