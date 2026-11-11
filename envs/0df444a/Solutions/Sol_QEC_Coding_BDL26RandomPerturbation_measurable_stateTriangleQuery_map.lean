-- Prove2me | solution 1 for QEC.Coding.BDL26RandomPerturbation.measurable_stateTriangleQuery_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-11T01:27:48.50506+00:00
-- url     : https://prove2.me/submissions/f9833d55-41ba-4644-bf07-733fbd68a2cf

import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_JointExecution
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_ActualExecutionCost
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_QEC_Coding_FiniteAlternatingConstruction_RandomPerturbation_CountedCostMeasurability
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_triangleQuery
import Theorems.Thm_QEC_Coding_BDL26RandomPerturbation_measurable_stateTrianglePointsQuery_map

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
    (P : TannerSquarePresentation) (lambda : ℝ) (t : Triangle P)
    (J : Ω → Vertex P → Space) (hJ : Measurable J)
    (L : List (Vertex P)) (f : Vertex P → Ω → ℕ × Space)
    (hf : ∀ u, Measurable (f u)) (z : Ω → Space) (hz : Measurable z) :
    Measurable (fun w => stateTriangleQuery P (J w) lambda t
      (L.map (fun u => (u, f u w))) (z w)) := by
  have hp := measurable_stateTrianglePointsQuery_map P lambda t J hJ L f hf
  have hq := measurable_triangleQuery
    (fun w => (stateTrianglePointsQuery P (J w) lambda t
      (L.map (fun u => (u, f u w)))).1) z (fun _ => (2 : ℝ))
    (fun i j => (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp
      ((measurable_pi_apply i).comp hp.fst))
    (fun j => (PiLp.continuous_apply (2 : ℝ≥0∞) (fun _ : Fin 3 => ℝ) j).measurable.comp hz)
    measurable_const
  have hc := (measurable_of_countable (fun ns : ℕ × ℕ => ns.1 + ns.2)).comp
    (hp.snd.prodMk hq.snd)
  exact hq.fst.prodMk hc
end QEC.Coding.BDL26RandomPerturbation
