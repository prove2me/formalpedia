-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.KerSelfDual.inv_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:47:58.987804+00:00
-- url     : https://prove2.me/submissions/0ec14c9d-c8b0-42ec-8618-032369942599

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualOfDiff
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualDifferent_Imports
import Theorems.Thm_PI_UnitaryGroupMassFormula_KerSelfDual_int_map
import Theorems.Thm_PI_UnitaryGroupMassFormula_KerSelfDual_one_map

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.KerSelfDual
namespace PI.UnitaryGroupMassFormula.KerSelfDual
theorem _root_.solution {E : Type} [Field E] [NumberField E] (cj : E ≃ₐ[ℚ] E) (hinv : ∀ x, cj (cj x) = x)
    (𝔟 𝔟c : Ideal (𝓞 E)) (hc : ∀ x : 𝓞 E, x ∈ 𝔟c ↔ ∃ y ∈ 𝔟, cj (y : E) = (x : E))
    (hb : 𝔟 ≠ ⊥) (hbc : 𝔟c ≠ ⊥) (y : E) :
    y ∈ ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ ↔
      cj y ∈ ((𝔟c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E))⁻¹ := by
  have hb0 : ((𝔟 : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hb
  have hbc0 : ((𝔟c : FractionalIdeal (nonZeroDivisors (𝓞 E)) E)) ≠ 0 :=
    FractionalIdeal.coeIdeal_ne_zero.mpr hbc
  rw [FractionalIdeal.mem_inv_iff hb0, FractionalIdeal.mem_inv_iff hbc0]
  constructor
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨w', hw', rfl⟩ := hw
    obtain ⟨b, hb𝔟, hbw⟩ := (hc w').mp hw'
    have h1 := h (algebraMap (𝓞 E) E b) (FractionalIdeal.mem_coeIdeal_of_mem _ hb𝔟)
    have h2 := one_map cj h1
    rw [map_mul] at h2
    have e : (algebraMap (𝓞 E) E w') = cj (algebraMap (𝓞 E) E b) := hbw.symm
    rw [e]
    exact h2
  · intro h w hw
    rw [FractionalIdeal.mem_coeIdeal] at hw
    obtain ⟨b, hb𝔟, rfl⟩ := hw
    obtain ⟨c, hcE⟩ := int_map cj b
    have hc𝔟 : c ∈ 𝔟c := (hc c).mpr ⟨b, hb𝔟, hcE.symm⟩
    have h1 := h (algebraMap (𝓞 E) E c) (FractionalIdeal.mem_coeIdeal_of_mem _ hc𝔟)
    rw [hcE, ← map_mul] at h1
    have h2 := one_map cj h1
    rw [hinv] at h2
    exact h2
end PI.UnitaryGroupMassFormula.KerSelfDual
