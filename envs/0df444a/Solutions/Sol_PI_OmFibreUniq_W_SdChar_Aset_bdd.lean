-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdChar.Aset_bdd
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:37.956259+00:00
-- url     : https://prove2.me/submissions/62443e2c-e98e-499e-815f-a84aff8912f6

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
theorem _root_.solution (hnt : ∃ y, ψ0 y ≠ 1) :
    ∃ y0 : Fv F v, y0 ≠ 0 ∧ ∀ t ∈ Aset v ψ0, ∃ s ∈ v.adicCompletionIntegers F, t = y0 * s := by
  obtain ⟨y, hy⟩ := hnt
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact hy (psi_zero v ψ0 hψa hψn)
  refine ⟨y, hy0, fun t ht => ⟨t / y, ?_, by field_simp⟩⟩
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  by_cases ht0 : t = 0
  · simp [ht0]
  rcases le_total (Valued.v (t / y)) 1 with hle | hge
  · exact hle
  · exfalso
    apply hy
    have hne : Valued.v (t / y) ≠ 0 := (Valuation.ne_zero_iff _).2 (div_ne_zero ht0 hy0)
    have hc : y / t ∈ v.adicCompletionIntegers F := by
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, ← inv_div, map_inv₀]
      calc (Valued.v (t / y))⁻¹ = (Valued.v (t / y))⁻¹ * 1 := (mul_one _).symm
        _ ≤ (Valued.v (t / y))⁻¹ * Valued.v (t / y) := by gcongr
        _ = 1 := inv_mul_cancel₀ hne
    have := (show ∀ c ∈ v.adicCompletionIntegers F, ψ0 (c * t) = 1 from ht) _ hc
    rwa [div_mul_cancel₀ _ ht0] at this
end PI.OmFibreUniq.W.SdChar
