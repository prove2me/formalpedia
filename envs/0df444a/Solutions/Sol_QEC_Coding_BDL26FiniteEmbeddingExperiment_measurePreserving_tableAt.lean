-- Prove2me | solution 1 for QEC.Coding.BDL26FiniteEmbeddingExperiment.measurePreserving_tableAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:40:30.784749+00:00
-- url     : https://prove2.me/submissions/cc6a459e-8ccc-44fc-9e35-ac0fc568631a

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Core
import Mathlib.Probability.Independence.Basic
import Mathlib.Dynamics.Ergodic.MeasurePreserving
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_FiniteExperiment_Laws
import Theorems.Thm_QEC_Coding_BDL26FiniteEmbeddingExperiment_measurePreserving_prefix

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26FiniteEmbeddingExperiment
open Classical MeasureTheory ProbabilityTheory
open BDL26RandomPerturbation
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open scoped ENNReal ProbabilityTheory
namespace QEC.Coding.BDL26FiniteEmbeddingExperiment
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (i : Fin n) :
    MeasurePreserving (tableAt p n i) (experimentLaw p n) (physicalTableLaw p i.val) :=
  measurePreserving_snd.comp (measurePreserving_prefix p i.isLt)
end QEC.Coding.BDL26FiniteEmbeddingExperiment
