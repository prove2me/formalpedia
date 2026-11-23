-- Prove2me | solution 1 for PI.VolStabSW.SdUniqW.mem_of_psi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:44:39.455799+00:00
-- url     : https://prove2.me/submissions/265a4352-070f-4fd6-8180-df7d2227d3bc

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_StabilizerOrbitVolume_SdUniq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabSW
open PI.VolStabSW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabSW.SdUniqW
theorem _root_.solution (ψ0 : Fv F v → ℂ) (r0 t : Fv F v) (h0 : ψ0 r0 ≠ 1)
    (ht : ∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) :
    t ∈ (fun s => r0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  by_contra hn
  have ht0 : t ≠ 0 := fun h => hn ⟨0, zero_mem _, by simp [h]⟩
  have hs : r0 * t⁻¹ ∉ v.adicCompletionIntegers F := fun hs => h0 (by
    have := ht _ hs
    rwa [inv_mul_cancel_right₀ ht0] at this)
  have hs0 : r0 * t⁻¹ ≠ 0 := fun h => hs (by rw [h]; exact zero_mem _)
  have hr0 : r0 ≠ 0 := fun h => hs0 (by rw [h, zero_mul])
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, not_le] at hs
  have hlt := ((Valued.v : Valuation (Fv F v) _).one_lt_val_iff hs0).mp hs
  refine hn ⟨(r0 * t⁻¹)⁻¹, (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (le_of_lt hlt), ?_⟩
  field_simp
end PI.VolStabSW.SdUniqW
