-- Prove2me | solution 1 for PI.OmLocU.Sd.vol_sq_mul_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:14:49.045212+00:00
-- url     : https://prove2.me/submissions/ff437138-e03d-49d7-a29e-c9b8aaa4e171

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_LocDensHI
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_LocalUnitaryOrbits_VolSqMulIndex
import Theorems.Thm_PI_OmLocU_Sd_vol_mul_vol_ann
import Theorems.Thm_PI_VolStabSW_measure_eq_relIndex_mul


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmLocU PI.OmLocU.Sd
open MeasureTheory PI.VolStabSW.SdUniqW Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
variable {V : Type} [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V] [T2Space V]
  [MeasurableSpace V] [BorelSpace V]
namespace PI.OmLocU.Sd
theorem _root_.solution {μ : Measure V} {χ : V → V → ℂ} (hμ : SelfDual μ χ)
    (hχ : ∀ x t y, χ (t + x) y = χ t y * χ x y) (h0 : ∀ y, χ y 0 = 1) (L L' : AddSubgroup V)
    (hLc : IsCompact (L : Set V)) (hLo : IsOpen (L : Set V))
    (hL'c : IsCompact (L' : Set V)) (hL'o : IsOpen (L' : Set V)) (hA : ann χ (L : Set V) = L')
    (hle : L ≤ L') (hN : L.relIndex L' ≠ 0) :
    μ.real (L : Set V) ^ 2 * (L.relIndex L' : ℝ) = 1 := by
  have := hμ.1
  have h1 := vol_mul_vol_ann hμ hχ h0 L L' hLc hLo hL'c hL'o hA
  have h2 := PI.VolStabSW.measure_eq_relIndex_mul μ L L' hle hL'o.measurableSet
    hLo.measurableSet hN
  have h3 : μ.real (L' : Set V) = (L.relIndex L' : ℝ) * μ.real (L : Set V) := by
    rw [measureReal_def, measureReal_def, h2, ENNReal.toReal_mul]
    simp
  rw [h3] at h1
  linarith [h1]
end PI.OmLocU.Sd
