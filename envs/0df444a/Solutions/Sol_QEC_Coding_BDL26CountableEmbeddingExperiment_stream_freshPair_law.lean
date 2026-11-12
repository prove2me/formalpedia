-- Prove2me | solution 1 for QEC.Coding.BDL26CountableEmbeddingExperiment.stream_freshPair_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T06:54:04.78654+00:00
-- url     : https://prove2.me/submissions/79c6d640-7827-43b2-a8b5-2705f060a1c2

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment_Core
import Mathlib.Probability.Independence.InfinitePi
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountableExperiment
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_truncate_law
import Theorems.Thm_QEC_Coding_BDL26CountableEmbeddingExperiment_measurable_truncate
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_freshPair_law
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurable_evaluate


set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26CountableEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26FiniteEmbeddingExperiment BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open scoped ENNReal ProbabilityTheory BigOperators
namespace QEC.Coding.BDL26CountableEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ) :
    (streamLaw p).map (fun omega => (levelMap p omega n, omega n)) =
      (outputLaw p n).prod (physicalTableLaw p n) := by
  let f : Experiment p (n+1) → StageMaps p n × StageTables p n :=
    fun z => (evaluate p n z.1, z.2)
  have hf : Measurable f := by
    have hfirst : Measurable (fun z : Experiment p (n+1) => evaluate p n z.1) :=
      @Measurable.comp (Experiment p (n+1)) (Experiment p n) (StageMaps p n)
        inferInstance inferInstance inferInstance (evaluate p n) Prod.fst
        (measurable_evaluate p n) measurable_fst
    exact hfirst.prodMk measurable_snd
  change (streamLaw p).map (f ∘ truncate p (n+1)) = _
  rw [← Measure.map_map hf (measurable_truncate p (n+1)), truncate_law]
  exact freshPair_law p n
end QEC.Coding.BDL26CountableEmbeddingExperiment
