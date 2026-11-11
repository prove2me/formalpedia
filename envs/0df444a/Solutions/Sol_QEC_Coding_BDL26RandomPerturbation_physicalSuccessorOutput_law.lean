-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.physicalSuccessorOutput_law
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T02:02:51.295237+00:00
-- url     : https://prove2.me/submissions/332ab266-9e01-4fb1-aa5e-e3582648dad1

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_GoodMapMeasurability
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_PhysicalSuccessor
import Mathlib.Probability.Kernel.Composition.Prod
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_EmbeddingKernel
section
noncomputable section
namespace QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26RXLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
private theorem map_freshTable_apply {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (ν : Measure B) [SFinite ν] (F : A × B → C) (hF : Measurable F) (a : A) :
    ((Kernel.id ×ₖ Kernel.const A ν).map F) a = ν.map (fun b => F (a,b)) := by
  have hslice : Measurable (fun b => F (a,b)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  ext s hs
  rw [Kernel.map_apply _ hF, Measure.map_apply hF hs,
    Kernel.id_prod_apply' _ _ (hF hs), Kernel.const_apply, Measure.map_apply hslice hs] <;> rfl
private theorem map_freshTable_law {A B C : Type*}
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace C]
    (μ : Measure A) (ν : Measure B) [SFinite ν]
    (F : A × B → C) (hF : Measurable F) :
    (μ.prod ν).map F = ((Kernel.id ×ₖ Kernel.const A ν).map F) ∘ₘ μ := by
  ext s hs
  rw [Measure.map_apply hF hs, Measure.prod_apply (hF hs),
    Measure.bind_apply hs (Kernel.aemeasurable _)]
  apply lintegral_congr
  intro a
  have hslice : Measurable (fun b => F (a,b)) :=
    hF.comp (measurable_const.prodMk measurable_id)
  rw [map_freshTable_apply ν F hF a, Measure.map_apply hslice hs] <;> rfl
end QEC.Coding.BDL26RandomPerturbation
end
end

set_option autoImplicit false
noncomputable section
open QEC QEC.Coding QEC.Coding.BDL26RandomPerturbation
open Classical BDL26FiniteTannerSquare BDL26ReplacementEmbedding BDL26RXLocalReplacement
open BDL26TannerLocalRegularity BDL26DecodingGraph
open BDL26RandomPhysicalLocality
open QEC.Coding.ProbabilisticConstruction.SphericalCap
open QEC.Coding.ProbabilisticConstruction.Resampling
open MeasureTheory ProbabilityTheory
namespace QEC.Coding.BDL26RandomPerturbation
theorem _root_.solution {L : ℝ} (p : GeometricParameters L) (n : ℕ)
    (μ : Measure (Vertex (state (perturbationOddScale p) n).presentation → Space))
    [IsProbabilityMeasure μ] :
    (μ.prod (physicalTableLaw p n)).map (fun z => physicalSuccessorOutput p n z.1 z.2) =
      (successorKernel p n) ∘ₘ μ := by
  exact map_freshTable_law μ (physicalTableLaw p n)
    (fun z => physicalSuccessorOutput p n z.1 z.2)
    (measurable_joint_physicalSuccessorOutput p n)
end QEC.Coding.BDL26RandomPerturbation
