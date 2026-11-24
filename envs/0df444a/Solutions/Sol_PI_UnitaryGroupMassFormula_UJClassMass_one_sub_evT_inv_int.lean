-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UJClassMass.one_sub_evT_inv_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T15:54:08.601947+00:00
-- url     : https://prove2.me/submissions/c2450dbc-196b-415e-9774-1dba00932d36

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_LSBase
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryApproxFin
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnitaryClassMass_OneSubEvTInvInt
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_af_sub_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_af_one_apply
import Theorems.Thm_PI_UnitaryGroupMassFormula_UJClassMass_evT_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField PI.UJClassFin PI.UnitaryGroupMassFormula.UJClassFin IsDedekindDomain
open scoped TensorProduct RestrictedProduct
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UJClassMass
open Classical
variable {F : Type} [Field F] [NumberField F]
variable (v : HeightOneSpectrum (𝓞 F))
namespace PI.UnitaryGroupMassFormula.UJClassMass
theorem _root_.solution (T : Set (HeightOneSpectrum (𝓞 F))) (t : 𝓞 F)
    (ht : ∀ w : HeightOneSpectrum (𝓞 F), w ∉ T → t ∉ w.asIdeal) :
    (1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹) ∈ intAf F := by
  intro w
  show ((1 - evT T) * algebraMap F (Af F) ((algebraMap (𝓞 F) F t)⁻¹)) w ∈ w.adicCompletionIntegers F
  rw [af_mul_apply, af_sub_apply, evT_apply, af_one_apply, af_alg_apply]
  split_ifs with hw
  · rw [sub_self, zero_mul]; exact zero_mem _
  · rw [sub_zero, one_mul, HeightOneSpectrum.mem_adicCompletionIntegers]
    have e1 : algebraMap F (w.adicCompletion F) ((algebraMap (𝓞 F) F t)⁻¹) =
        (((algebraMap (𝓞 F) F t)⁻¹ : F) : w.adicCompletion F) := rfl
    rw [e1, HeightOneSpectrum.valuedAdicCompletion_eq_valuation', map_inv₀,
      HeightOneSpectrum.valuation_of_algebraMap,
      (HeightOneSpectrum.intValuation_eq_one_iff_mem_primeCompl w t).2 (ht w hw), inv_one]
end PI.UnitaryGroupMassFormula.UJClassMass
