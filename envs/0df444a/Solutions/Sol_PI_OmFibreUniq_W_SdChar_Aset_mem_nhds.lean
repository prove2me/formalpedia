-- Prove2me | solution 1 for PI.OmFibreUniq.W.SdChar.Aset_mem_nhds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:09:35.165302+00:00
-- url     : https://prove2.me/submissions/2b022973-c59a-4e86-bb17-40d5f64a8d98

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_ExistsUnifFv
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DetAdmA
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HaarFibreUniqueness_SdExChar
import Theorems.Thm_PI_OmFibreUniq_W_SdChar_eq_one_of_pow_near
import Theorems.Thm_PI_OmFibreUniq_W_SdChar_psi_zero
import Theorems.Thm_PI_OmFibreUniq_W_SdChar_psi_natCast_mul
import Theorems.Thm_PI_VolStabSW_HasDens_sub


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
include hψc hψa hψn
namespace PI.OmFibreUniq.W.SdChar
theorem _root_.solution : Aset v ψ0 ∈ 𝓝 (0 : Fv F v) := by
  have h0 : ψ0 0 = 1 := psi_zero v ψ0 hψa hψn
  have hU : {x | ‖ψ0 x - 1‖ < 1} ∈ 𝓝 (0 : Fv F v) := by
    apply (isOpen_lt (hψc.sub continuous_const).norm continuous_const).mem_nhds
    simp [h0]
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds_zero.mp hU
  apply Filter.mem_of_superset (Valued.mem_nhds_zero.mpr ⟨γ, subset_rfl⟩)
  intro t ht c hc
  have hin : ∀ c' ∈ v.adicCompletionIntegers F, ‖ψ0 (c' * t) - 1‖ < 1 := by
    intro c' hc'
    apply hγ
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers,
      ← Valuation.restrict_le_one_iff] at hc'
    simp only [Set.mem_setOf_eq, map_mul]
    calc Valued.v.restrict c' * Valued.v.restrict t ≤ 1 * Valued.v.restrict t := by gcongr
      _ = Valued.v.restrict t := one_mul _
      _ < _ := ht
  apply eq_one_of_pow_near _ (hψn _)
  intro m
  rw [← psi_natCast_mul v ψ0 hψa hψn, ← mul_assoc]
  exact hin _ (mul_mem (natCast_mem _ m) hc)
end PI.OmFibreUniq.W.SdChar
