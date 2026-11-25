-- Prove2me | solution 1 for PI.UnitaryApproxFinWork.weak_approximation_finite_unitary
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T10:47:05.919398+00:00
-- url     : https://prove2.me/submissions/fae3ca00-8fd0-4bba-9d43-52c188517fca

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproxF
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryApproximation_WeakApproximationFiniteUnitary
import Theorems.Thm_PI_UnitaryApproxFinWork_wa_valued_algebraMap
import Theorems.Thm_PI_UnitaryApproxFinWork_wa_exists_close
import Theorems.Thm_PI_UnitaryApproxFinWork_wa_exists_int_approx

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum
open PI PI.UnitaryApproxFinWork
variable {F : Type} [Field F] [NumberField F]
namespace PI.UnitaryApproxFinWork
theorem _root_.solution : WeakApproxF := by
  intro F _ _ T c D hD
  have hDF : ((D : 𝓞 F) : F) ≠ 0 := by
    first
      | exact_mod_cast hD
      | exact (RingOfIntegers.coe_ne_zero_iff).mpr hD
      | (intro h; exact hD (Subtype.ext h))
  choose b hb using fun v : HeightOneSpectrum (𝓞 F) =>
    wa_exists_close v (c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹)
  obtain ⟨a', ha'⟩ := wa_exists_int_approx T b
  refine ⟨(D : F) * a', fun v hv => ?_⟩
  have hdv0 : algebraMap F (v.adicCompletion F) (D : F) ≠ 0 := (map_ne_zero _).mpr hDF
  refine ⟨c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) a', ?_, ?_⟩
  · rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
    have e1 : c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) a' =
        (c v * (algebraMap F (v.adicCompletion F) (D : F))⁻¹ - algebraMap F (v.adicCompletion F) (b v)) +
          algebraMap F (v.adicCompletion F) (b v - a') := by
      rw [map_sub]
      ring
    rw [e1]
    refine le_trans (Valuation.map_add _ _ _) (max_le (hb v).le ?_)
    rw [wa_valued_algebraMap, Valuation.map_sub_swap]
    exact ha' v hv
  · rw [map_mul, mul_sub, mul_comm (algebraMap F (v.adicCompletion F) (D : F)) (c v * _), mul_assoc,
      inv_mul_cancel₀ hdv0, mul_one]
end PI.UnitaryApproxFinWork
