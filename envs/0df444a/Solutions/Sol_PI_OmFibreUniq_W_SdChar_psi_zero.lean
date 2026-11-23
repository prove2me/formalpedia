-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdChar.psi_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:23:02.377176+00:00
-- url     : https://prove2.me/submissions/6e7f2c11-c34c-421b-ac35-eca51601c00d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.OmFibreUniq PI.OmFibreUniq.W PI.OmFibreUniq.W.SdChar
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory Topology Filter NumberField IsDedekindDomain
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
  (ψ0 : Fv F v → ℂ) (hψc : Continuous ψ0) (hψa : ∀ r s, ψ0 (r + s) = ψ0 r * ψ0 s)
  (hψn : ∀ r, ‖ψ0 r‖ = 1)
include hψa hψn
namespace PI.OmFibreUniq.W.SdChar
theorem _root_.solution : ψ0 0 = 1 := by
  have h := hψa 0 0
  rw [add_zero] at h
  have hne : ψ0 0 ≠ 0 := by
    intro h0
    have := hψn 0
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have h2 : ψ0 0 * (ψ0 0 - 1) = 0 := by rw [mul_sub, mul_one, ← h, sub_self]
  exact sub_eq_zero.mp ((mul_eq_zero.mp h2).resolve_left hne)
end PI.OmFibreUniq.W.SdChar
