-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdCore.zero_mem_ann
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:09:38.800916+00:00
-- url     : https://prove2.me/submissions/4ff08761-84b4-458e-9133-888be656dcad

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExCore
import Theorems.Thm_PI_OmFibreUniq_W_SdCore_chi_zero_left

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
namespace PI.OmFibreUniq.W.SdCore
theorem _root_.solution (χ : V → V → ℂ) (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y)
    (hsym : ∀ x y, χ x y = χ y x) (hn : ∀ x y, ‖χ x y‖ = 1) (L : Set V) : (0 : V) ∈ ann χ L := by
  intro x _
  rw [hsym]
  exact chi_zero_left χ hχ hn x
end PI.OmFibreUniq.W.SdCore
