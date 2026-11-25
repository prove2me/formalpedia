-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdChar.psi_natCast_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:01:18.053791+00:00
-- url     : https://prove2.me/submissions/11a8f90f-325c-4c3b-ae34-a30d7b8bf45b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Theorems.Thm_PI_OmFibreUniq_W_SdChar_psi_zero

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
theorem _root_.solution (m : ℕ) (t : Fv F v) : ψ0 ((m : Fv F v) * t) = ψ0 t ^ m := by
  induction m with
  | zero => simp [psi_zero v ψ0 hψa hψn]
  | succ m ih =>
    rw [Nat.cast_succ, add_mul, one_mul, hψa, ih, pow_succ]
end PI.OmFibreUniq.W.SdChar
