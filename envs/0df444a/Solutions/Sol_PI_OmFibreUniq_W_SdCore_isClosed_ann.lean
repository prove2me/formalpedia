-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdCore.isClosed_ann
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:38:22.759143+00:00
-- url     : https://prove2.me/submissions/6a605f98-fda7-4eb6-a0ed-5f0a4b187bbb

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdCore
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter
open PI.VolStabSW.SdUniqW
open scoped ENNReal
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [LocallyCompactSpace V] [SecondCountableTopology V] [MeasurableSpace V] [BorelSpace V]
variable (χ : V → V → ℂ) (hχc : Continuous (fun p : V × V => χ p.1 p.2))
  (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (hsym : ∀ x y, χ x y = χ y x)
  (hn : ∀ x y, ‖χ x y‖ = 1)
  (μ : Measure V) [μ.IsAddHaarMeasure] (M : AddSubgroup V) (hMc : IsCompact (M : Set V))
  (hMo : IsOpen (M : Set V))
include hχc
namespace PI.OmFibreUniq.W.SdCore
theorem _root_.solution : IsClosed (ann χ (M : Set V)) := by
  have : ann χ (M : Set V) = ⋂ x ∈ (M : Set V), {y | χ x y = 1} := by
    ext y; simp [ann]
  rw [this]
  exact isClosed_biInter fun x _ =>
    isClosed_eq (hχc.comp (continuous_const.prodMk continuous_id)) continuous_const
end PI.OmFibreUniq.W.SdCore
