-- Prove2me | solution 1 for PI.SelfDualLoc.W.unitLoc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:38.492244+00:00
-- url     : https://prove2.me/submissions/d0f1284a-46d1-41b8-ae5f-c7e4456ad597

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_SelfDualLoc
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_DualBasis
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_SelfDualLocalBasis_OneTmulMemOloc
import Theorems.Thm_PI_SelfDualLoc_W_inclE_apply
import Theorems.Thm_PI_SelfDualLoc_W_one_tmul_mem_Oloc

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix NumberField IsDedekindDomain
open scoped TensorProduct
noncomputable section
open PI PI.SelfDualLoc PI.SelfDualLoc.W
open PI.SelfDualLoc
variable {F E : Type} [Field F] [Field E] [Algebra F E]
variable [NumberField F] [NumberField E]
namespace PI.SelfDualLoc.W
theorem _root_.solution : UnitLoc := by
  intro F E _ _ _ _ _ v s hs
  have hs0 : (s : F) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact v.asIdeal.zero_mem
  set a : v.adicCompletion F := algebraMap F (v.adicCompletion F) (s : F) with ha
  have ha0 : a ≠ 0 := by
    rw [ha]; exact (map_ne_zero _).2 hs0
  have hval : Valued.v a = 1 := by
    have h1 : v.valuation F (algebraMap (𝓞 F) F s) = 1 := by
      rw [IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap]
      refine le_antisymm (v.intValuation_le_one s) (not_lt.1 fun h => hs ?_)
      first
        | exact (v.intValuation_lt_one_iff_mem s).1 h
        | exact (Ideal.dvd_span_singleton).1 ((v.intValuation_lt_one_iff_dvd s).1 h)
    rw [ha, ← h1]
    first
      | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v (algebraMap (𝓞 F) F s)
      | exact IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation v (algebraMap (𝓞 F) F s)
      | rfl
  have hmem : a⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval, inv_one]
  refine ⟨(1 : E) ⊗ₜ[F] a⁻¹, one_tmul_mem_Oloc v hmem, ?_⟩
  rw [inclE_apply, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, Algebra.smul_def, mul_one, ← ha,
    mul_inv_cancel₀ ha0]
  rfl
end PI.SelfDualLoc.W
