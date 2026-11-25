-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdCore.chi_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T10:01:01.244335+00:00
-- url     : https://prove2.me/submissions/f3c828bc-307c-47c9-9148-7fc06c01110c

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
namespace PI.OmFibreUniq.W.SdCore
theorem _root_.solution (χ : V → V → ℂ) (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y)
    (hn : ∀ x y, ‖χ x y‖ = 1) (y : V) : χ 0 y = 1 := by
  have h := hχ 0 0 y
  rw [add_zero] at h
  have hne : χ 0 y ≠ 0 := by
    intro h0
    have := hn 0 y
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h2 : χ 0 y * (χ 0 y - 1) = 0 := by rw [mul_sub, ← h, mul_one, sub_self]
  rcases mul_eq_zero.1 h2 with h1 | h1
  · exact absurd h1 hne
  · exact sub_eq_zero.1 h1
end PI.OmFibreUniq.W.SdCore
