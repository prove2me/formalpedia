-- Prove2me | solution 1 for PI.VolStabW.SdUniqW.mem_of_psi
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:58:15.098805+00:00
-- url     : https://prove2.me/submissions/e35eec34-c966-45c5-a199-0b587014461a

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_RestrProd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_TensTop
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_DensFibV
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_AdelicLocalCompactness_AdeleLC
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeilStabilizerVolume_SdUniq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.VolStabW
open PI.VolStabW.SdUniqW
open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.AdicCompletionValuation
  PI.VolFromSW
variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))
namespace PI.VolStabW.SdUniqW
theorem _root_.solution (ψ0 : Fv F v → ℂ) (r0 t : Fv F v) (h0 : ψ0 r0 ≠ 1)
    (ht : ∀ s ∈ v.adicCompletionIntegers F, ψ0 (s * t) = 1) :
    t ∈ (fun s => r0 * s) '' (v.adicCompletionIntegers F : Set (Fv F v)) := by
  by_cases ht0 : t = 0
  · exact ⟨0, (v.adicCompletionIntegers F).zero_mem, by simp [ht0]⟩
  have hr : r0 ≠ 0 := by
    rintro rfl
    exact h0 (by simpa using ht 0 (v.adicCompletionIntegers F).zero_mem)
  by_cases hle : Valued.v r0 ≤ Valued.v t
  · exfalso
    apply h0
    have hs : r0 / t ∈ v.adicCompletionIntegers F := by
      rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
      exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 ht0))).2 hle
    have h2 := ht _ hs
    rwa [div_mul_cancel₀ _ ht0] at h2
  · push_neg at hle
    refine ⟨t / r0, ?_, by field_simp⟩
    rw [SetLike.mem_coe, HeightOneSpectrum.mem_adicCompletionIntegers, map_div₀]
    exact (div_le_one₀ (zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hr))).2 hle.le
end PI.VolStabW.SdUniqW
